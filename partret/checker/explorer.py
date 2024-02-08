#!/usr/bin/env python3

# TODO: license

from datetime import datetime
import json
import os
import sys

from partret.checker.checker import Checker
from partret.config import Config
from partret.solver.icarus import IcarusSolver
from partret.solver.jasper import JasperSolver
from partret.util.generic import rename_to_test_sig
from partret.util.image import Image

class Explorer(Checker):
    """ TODO """

    def __init__(self, config, logger, workdir, verbosity=0):
        """ constructor """
        
        super().__init__(config, logger, workdir, verbosity)

        # destination
        assert isinstance(config['dst'], str)
        self._dst = Image(self._logger, config['dst'])

        #self._unknown_regs = self._regs - self._ret_regs - self._non_ret_regs
        self._reg_batches = None

        self._iv_solver = IcarusSolver(config, logger, workdir)
    

    def minimize_retention_list(self):
        """ minimize the number of retention registers from a complete retention list """
        
        self._unknown_regs |= set(self._ret_regs)
        self._ret_regs = set()

        self._solve()

        assert not self._unknown_regs
        assert self._regs == (self._ret_regs | self._non_ret_regs)

    
    def complete_retention_list(self):
        """ Expand an incomplete retention list to include all necessary retention registers """
        
        # create proof script for Jasper
        # TODO: modify this
        ret_checker = self._gen_ret_checker(get_trace_info=True)

        # Debug
        #with open(os.path.join(self._workdir, 'test.tcl'), 'w') as fw:
        #    print('\n'.join(ret_checker), file=fw)
        
        ret_by_cex = []
        while len(self._unknown_regs) > 0:
            # record current progress
            self._report_current_progress()

            # generate formal testbench
            # TODO: modify this
            self._gen_wrapper_script(self._ret_regs)

            # Debug
            import subprocess
            subprocess.run(['cp', os.path.join(self._workdir, 'wrapper.v'), os.path.join(self._workdir, 'wrapper_formal.sv')], stdout=subprocess.PIPE)

            # launch Jasper
            out_msg = self._solver._exec_jg(ret_checker)

            # Debug
            with open(os.path.join(self._workdir, 'out_msg.txt'), 'w') as fw:
                print(out_msg, file=fw)

            # parse Jasper output
            res = self._solver._parse_jg_result(out_msg)
            self._logger.dump(res)

            if JasperSolver.is_proven(res):
                # all unknown registers can be safely non-retained

                self._non_ret_regs |= self._unknown_regs
                self._unknown_regs = set()
            elif JasperSolver.is_cex(res):
                # extract cex trace info
                input_vals = self._solver.extract_cex_trace_info(out_msg, list(self._input_width_list.keys()))
                check_cond_vals = self._solver.extract_cex_trace_info(out_msg, ['check_cond'])['check_cond']

                #ret_candids = list(self._unknown_regs.copy())
                ret_candids = self._solver.get_retention_candidates(out_msg)
                
                # Debug
                self._logger.dump('Retention candidates:')
                self._logger.dump('\n'.join(ret_candids))

                new_ret = []
                while len(ret_candids) > 0:
                    candid = ret_candids.pop()

                    # create simulation testbench
                    self._gen_wrapper_script(self._ret_regs | set(new_ret + ret_candids), [check_cond_vals, input_vals])

                    # simulate
                    sim_msg = self._iv_solver.exec(self._get_design_files())

                    # Debug
                    #self._logger.dump('Remove {}:'.format(candid))
                    #self._logger.dump(sim_msg.strip().split('\n')[-1])
                    
                    # extend retention list
                    if IcarusSolver.is_cex(sim_msg):
                        new_ret.append(candid)

                assert len(new_ret) > 0
                
                self._logger.dump('Registers added to retention list:')
                self._logger.dump('\n'.join(new_ret))

                ret_by_cex += new_ret
                self._ret_regs |= set(new_ret)
                self._unknown_regs -= set(new_ret)
            else:
                self._logger.dump('Error: Failed to prove property within {}s.'.format(Config.DEFAULT_TIMEOUT))
                self._logger.dump('The registers in the retention list are necessary but may not be suffincient.')
                self._logger.dump('Exitting...')
                sys.exit(0)

            # record the solution
            self._dst.take_screenshot(self._ret_regs, self._non_ret_regs, self._unknown_regs, {'ret_by_cex': ret_by_cex})
        
        assert not self._unknown_regs
        assert self._regs == (self._ret_regs | self._non_ret_regs)

    
    def _solve(self):
        """ Analyze the registers in self._unknown_regs and put them into self._ret_regs/self._non_ret_regs """
        
        target_regs = self._get_target_regs()
        while target_regs:
            # record current progress
            self._report_current_progress()
            self._logger.dump('Check registers:')
            self._logger.dump('\n'.join(target_regs))

            r_toret = self._ret_regs | (self._unknown_regs - target_regs)

            # generate proof scripts
            # TODO: modify this
            self._gen_wrapper_script(r_toret)
            # TODO: modify this
            #ret_checker = self._gen_ret_checker(r_toret)
            ret_checker = self._gen_ret_checker()
            #self._logger.dump('\n'.join(ret_checker))

            # launch Jasper
            out_msg = self._solver._exec_jg(ret_checker)
            #self._logger.dump(out_msg)

            # parse Jasper output
            res = self._solver._parse_jg_result(out_msg)
            self._logger.dump(res)

            if JasperSolver.is_proven(res):
                self._non_ret_regs |= target_regs
            elif len(target_regs) == 1:
                self._ret_regs |= target_regs
            
            self._unknown_regs -= (self._ret_regs | self._non_ret_regs)
            target_regs = self._get_target_regs()

            # record the current solution
            self._dst.take_screenshot(self._ret_regs, self._non_ret_regs, self._unknown_regs)

            #sys.exit(0)

    
    def _gen_wrapper_script(self, ret_list, trace_info=None):
        """ Profile wrapper.v with a specific retention list """

        wrapper = os.path.join(self._workdir, 'wrapper.v')
        
        wrapper_lines = self._gen_wrapper(ret_list, trace_info)

        with open(wrapper, 'w') as fw:
            print('\n'.join(wrapper_lines), file=fw)
    
    
    def _get_target_regs(self):
        """ Returns a batch (set) of target registers for the next retention check """
        
        # initialize register batches if not already
        if self._reg_batches is None:
            b_neighbor = [frozenset(self._get_regs_of_same_module(r, self._unknown_regs)) for r in self._unknown_regs]
            b_friend = [frozenset(self._get_regs_with_similar_names(r, self._unknown_regs)) for r in self._unknown_regs]
            b_copy = [frozenset(self._get_copied_regs(r, self._unknown_regs)) for r in self._unknown_regs]
            b_raw = [frozenset([r]) for r in self._unknown_regs]

            b_all = set(b_neighbor) | set(b_friend) | set(b_copy) | set(b_raw)
        
            self._reg_batches = [set(fs) for fs in b_all]

        # update, unify, and sort
        self._reg_batches = set([frozenset(b - self._ret_regs - self._non_ret_regs) for b in self._reg_batches])
        self._reg_batches = [set(fs) for fs in self._reg_batches]
        self._reg_batches = [b for b in self._reg_batches if b]
        self._reg_batches.sort(key=lambda b: len(b), reverse=False)

        #self._logger.dump(self._reg_batches)
        
        self._logger.dump(
            '#remaining batches: {}'.format(len(self._reg_batches)))

        # pop the last (largest) batch
        return self._reg_batches.pop() if self._reg_batches else None
    

    """ Utility functions """

    def _get_regs_of_same_module(self, target, pool):
        """ Get the registers that are in the same module as the target register """
        
        def _is_same_module(a, b):
            """ Compare two paths to check if is of a same module """

            # same length and only diff at the tail
            return len(a) == len(b) and a[:-1] == b[:-1]
        
        t_path = target.split('.')
        neighbors = [
            reg for reg in pool if _is_same_module(
                t_path, reg.split('.')
            )
        ]
        return neighbors
    
    def _get_regs_with_similar_names(self, target, pool):
        """ Get the regs that have similar names as the target """

        def _diff_in_digits(a, b):
            """ Differ only in digits """

            def _remove_digits(in_str):
                return ''.join([c for c in in_str if not c.isdigit()])

            return _remove_digits(a) == _remove_digits(b)

        def _diff_in_suffix(a, b):
            """ Differ only in the last suffix """

            return (a.split('_')[:-1] == b.split('_')[:-1]) if '_' in a else False

        def _is_similar(a, b):
            """ Compare tails of two paths """

            tail_a = a.split('.')[-1]
            tail_b = b.split('.')[-1]

            return _diff_in_digits(
                tail_a, tail_b) or _diff_in_suffix(tail_a, tail_b)

        return [reg for reg in pool if _is_similar(target, reg)]
    
    def _get_copied_regs(self, target, pool):
        """ Get the copied regs (1-diff in the prefix) """

        def _is_copy(a, b):
            """ Compare two paths to check if is a copy """

            # same length and same ending
            if len(a) != len(b) or a[-1] != b[-1]:
                return False

            # exact 1-diff (other criteria?)
            diff = [i[0] != i[1] for i in zip(a, b)]
            return diff.count(True) == 1
            #count = list(itertools.accumulate(diff))
            #return count[-1] == 1

        t_path = target.split('.')
        copies = [reg for reg in pool if _is_copy(t_path, reg.split('.'))]
        copies = copies + [target] if len(copies) > 0 else []
        return copies

    def _report_current_progress(self):
        """ Report current progress """

        self._logger.fence()
        self._logger.dump('Current progress ({}):'.format(datetime.now()))
        self._logger.dump('#total:         {}'.format(len(self._regs)))
        self._logger.dump('#unknown:       {}'.format(len(self._unknown_regs)))
        self._logger.dump('#retention:     {}'.format(len(self._ret_regs)))
        self._logger.dump('#non retention: {}'.format(len(self._non_ret_regs)))
    