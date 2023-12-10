#!/usr/bin/env python3

# TODO: license

from datetime import datetime
import json
import os
import sys

from partret.checker.checker import Checker
from partret.config import Config
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
    

    def minimize_retention_list(self):
        """ minimize the number of retention registers from a complete retention list """
        
        self._unknown_regs |= set(self._ret_regs)
        self._ret_regs = set()

        self._solve()

        assert not self._unknown_regs
        assert self._regs == (self._ret_regs | self._non_ret_regs)

    
    def complete_retention_list(self):
        """ Expand an incomplete retention list to include all necessary retention registers """
        
        # Temporary files
        # - cex_info.tcl: records the register values during the last standby state
        cex_info_file = os.path.join(self._workdir, 'cex_info.tcl')
        
        #self._unknown_regs = set(self._non_ret_regs)
        #self._non_ret_regs = set()

        ret_by_cex = set()
        while len(self._unknown_regs) > 0:
            # record current progress
            self._report_current_progress()

            # generate proof scripts
            #self._gen_wrapper_script(self._ret_regs | ret_by_cex)
            self._gen_wrapper_script(self._ret_regs)
            #ret_checker = self._gen_ret_checker(self._ret_regs)
            ret_checker = self._gen_ret_checker()

            # add commands for extracting cex trace info
            assert ret_checker[-1] == 'exit'
            ret_checker.pop()
            
            ret_checker += [
                '',
                'set result [get_property_info output_equiv -list status]',
                'if { $result != "cex" } {',
                '   exit',
                '}',
                'visualize -violation -property output_equiv',
                '',
                'set sc [visualize -get_value standby_cond -radix 2]',
                #'set index -1',
                'for {set i [expr [llength $sc] - 1]} {$i >= 2} {incr i -1} {',
                '   set prev_1 [lindex $sc [expr $i - 1]]',
                '   set prev_2 [lindex $sc [expr $i - 2]]',
                '   if { $prev_1 == "1\'b1" && $prev_2 == "1\'b0" } {',
                '       set index $i',
                '       break',
                '   }',
                '}',
                'visualize -save -init_state {} -cycle [expr $index + 1] -force'.format(cex_info_file),
                ''
            ]

            ret_checker.append('exit')

            # Debug
            #with open(os.path.join(self._workdir, 'test.tcl'), 'w') as fw:
            #    print('\n'.join(ret_checker), file=fw)
            #self._logger.dump('\n'.join(ret_checker))
            #sys.exit(0)
            
            # launch Jasper
            out_msg = self._solver._exec_jg(ret_checker)

            # Debug
            #with open(os.path.join(self._workdir, 'out_msg.txt'), 'w') as fw:
            #    print(out_msg, file=fw)

            # parse Jasper output
            res = self._solver._parse_jg_result(out_msg)
            self._logger.dump(res)

            if JasperSolver.is_proven(res):
                # all unknown registers can be safely non-retained

                self._non_ret_regs |= self._unknown_regs
                self._unknown_regs = set()
            else:
                # extend retention list

                reg_vals_golden = {}
                reg_vals_test = {}
                
                with open(cex_info_file, 'r') as fr:
                    for line in fr:
                        line = line.strip()     # remove '\n' at the end
                        reg = line.split()[0]
                        val = line.split()[1]

                        if reg.startswith('design_golden'):
                            reg_vals_golden['.'.join(reg.split('.')[1:])] = val
                        elif reg.startswith('design_test'):
                            reg_vals_test['.'.join(reg.split('.')[1:])] = val
                        else:
                            self._logger.dump('Warning: register {} is not contained in either the golden or test design'.format(reg))
                
                reg_diff_vals = []
                for reg_golden in reg_vals_golden:
                    reg_test = rename_to_test_sig(reg_golden)
                    if reg_test in reg_vals_test and reg_vals_golden[reg_golden] != reg_vals_test[reg_test]:
                        reg_diff_vals.append(reg_golden)

                self._logger.dump('Registers added to retention list:')
                self._logger.dump('\n'.join(reg_diff_vals))

                ret_by_cex |= set(reg_diff_vals)
                self._ret_regs |= set(reg_diff_vals)
                self._unknown_regs -= set(reg_diff_vals)

            # record the solution
            self._dst.take_screenshot(self._ret_regs, self._non_ret_regs, self._unknown_regs, {'ret_by_cex': ret_by_cex})

        assert not self._unknown_regs
        assert self._regs == (self._ret_regs | self._non_ret_regs)

        if self._verbosity == 0:
            os.remove(cex_info_file)

    
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
            self._gen_wrapper_script(r_toret)
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

    
    def _gen_wrapper_script(self, ret_list):
        """ Profile wrapper.v with a specific retention list """

        wrapper = os.path.join(self._workdir, 'wrapper.v')
        
        wrapper_lines = self._gen_wrapper(ret_list)

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
    