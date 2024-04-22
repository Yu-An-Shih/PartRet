#!/usr/bin/env python3

# TODO: license

from datetime import datetime
import itertools
import json
import os
import sys

from partret.checker.checker import Checker
from partret.config import Config
from partret.solver.simulator import IcarusSolver
#from partret.solver.simulator import VCSSolver
from partret.solver.jasper import JasperSolver
from partret.solver.yosys import YosysSolver
#from partret.util.generic import rename_to_test_sig
from partret.util.image import Image
from partret.util.timer import Timer

class Explorer(Checker):
    """ Automatic tool to determine the optimal retention register list """

    def __init__(self, config, logger, workdir, verbosity=0):
        """ constructor """
        
        # Sanity checks
        self._retention_checker = os.path.join(workdir, 'ret_checker.tcl')
        assert os.path.isfile(self._retention_checker)
        
        super().__init__(config, logger, workdir, verbosity)

        # destination
        assert isinstance(config['dst'], str)
        self._dst = Image(self._logger, config['dst'])

        #self._unknown_regs = self._regs - self._ret_regs - self._non_ret_regs
        self._reg_batches = None

        self._simulator = IcarusSolver(config, self._design_files, logger, workdir)
        #self._simulator = VCSSolver(config, self._design_files, logger, workdir)

        # Timing information
        self._timer = Timer(logger)
    

    def minimize_retention_list(self):
        """ Analyze the registers in self._unknown_regs and put them into self._ret_regs/self._non_ret_regs """
        ### Recommended use case: minimize the number of retention registers from a complete retention list ###

        # create proof script for Jasper
        with open(self._retention_checker, 'r') as fr:
            ret_checker = [ line.strip('\n') for line in fr.readlines() ]
        
        ret_checker += ['exit']
        
        target_regs = self._get_target_regs()
        while target_regs:
            # record current progress
            self._report_current_progress()
            self._logger.dump('Check registers:')
            self._logger.dump('\n'.join(target_regs))

            #r_toret = self._ret_regs | (self._unknown_regs - target_regs)
            r_noret = self._non_ret_regs | target_regs

            # generate partial retention design
            self._gen_partret_design(r_noret)

            # launch Jasper
            out_msg = self._solver._exec_jg(ret_checker)
            #self._logger.dump(out_msg)

            # parse Jasper output
            res = self._solver._parse_jg_result(out_msg)
            self._logger.dump(res)

            # update timing information
            self._timer.update_time(res['output_equiv'])
            
            if JasperSolver.is_proven(res):
                self._non_ret_regs |= target_regs
            elif JasperSolver.is_cex(res):
                if len(target_regs) == 1:
                    self._ret_regs |= target_regs
            else:
                self._logger.dump('Error: Failed to prove property within {}s.'.format(Config.DEFAULT_VERIF_TIMEOUT))
                self._logger.dump('The registers in the retention list are sufficient but may not be necessary.')
                self._logger.dump('Exitting...')
                break
            
            self._unknown_regs -= (self._ret_regs | self._non_ret_regs)
            target_regs = self._get_target_regs()

            # record the current solution
            self._dst.take_screenshot(self._ret_regs, self._non_ret_regs, self._unknown_regs)

            # Check for timeout
            if self._timer.get_elapsed_time() > Config.DEFAULT_TIMEOUT:
                self._logger.dump('Timeout: Solving time ({}s) is larger than {}s.'.format(self._timer.get_elapsed_time(), Config.DEFAULT_TIMEOUT))
                self._logger.dump('Exitting...')
                break

        #assert not self._unknown_regs
        #assert self._regs == (self._ret_regs | self._non_ret_regs)

        # report solving information
        self._report_solving_info()

    
    def complete_retention_list(self):
        """ Expand an incomplete retention list to include all necessary retention registers """
        
        # create proof script for Jasper
        with open(self._retention_checker, 'r') as fr:
            ret_checker = [ line.strip('\n') for line in fr.readlines() ]
        
        ret_checker += self._gen_trace_info_getter()
        ret_checker += ['exit']

        # Debug
        #with open(os.path.join(self._workdir, 'test.tcl'), 'w') as fw:
        #    print('\n'.join(ret_checker), file=fw)
        
        ret_by_cex = []
        while len(self._unknown_regs) > 0:
            # record current progress
            self._report_current_progress()

            # generate partial retention design
            self._gen_partret_design(self._non_ret_regs | self._unknown_regs)

            # Debug
            #import subprocess
            #subprocess.run(['cp', os.path.join(self._workdir, 'design_test.v'), os.path.join(self._workdir, 'design_test_formal.v')])
            
            # launch Jasper
            out_msg = self._solver._exec_jg(ret_checker)

            # Debug
            #with open(os.path.join(self._workdir, 'out_msg.txt'), 'w') as fw:
            #    print(out_msg, file=fw)

            # parse Jasper output
            res = self._solver._parse_jg_result(out_msg)
            self._logger.dump(res)

            # update timing information
            self._timer.update_time(res['output_equiv'])

            if JasperSolver.is_proven(res):
                # all unknown registers can be safely non-retained

                self._non_ret_regs |= self._unknown_regs
                self._unknown_regs = set()
            elif JasperSolver.is_cex(res):
                # extract cex trace info
                input_vals = self._solver.extract_cex_trace_info(out_msg, list(self._input_width_list.keys()) + ['pr_restore'])
                check_cond_vals = self._solver.extract_cex_trace_info(out_msg, ['check_cond'])['check_cond']

                # create simulation testbench
                self._gen_wrapper_sim([check_cond_vals, input_vals])

                #ret_candids = list(self._unknown_regs.copy())
                ret_candids = self._solver.get_retention_candidates(out_msg)

                assert set(ret_candids) & self._ret_regs == set()
                
                # TODO: add this line? need to deal with (human) error cases
                #ret_candids -= self._non_ret_regs
                
                # Print the candidate retention registers
                if self._verbosity > 0:
                    self._logger.dump('Retention candidates:')
                    self._logger.dump('\n'.join(ret_candids))
                
                new_ret = []
                while len(ret_candids) > 0:
                    candid = ret_candids.pop()
                    #candid = ret_candids.pop(0)

                    # generate partial retention design
                    # TODO: for simulation, create a large power-collapsible design instead?
                    self._gen_partret_design(self._non_ret_regs | (self._unknown_regs - set(new_ret + ret_candids)))

                    # simulate
                    sim_msg = self._simulator.exec()

                    # Debug
                    #self._logger.dump('Remove {}:'.format(candid))
                    #self._logger.dump(sim_msg.strip().split('\n')[-1])                     # Icarus
                    #self._logger.dump(sim_msg.split('$finish')[0].strip().split('\n')[-1]) # VCS
                    
                    # extend retention list
                    if IcarusSolver.is_cex(sim_msg):
                    #if VCSSolver.is_cex(sim_msg):
                        new_ret.append(candid)

                assert len(new_ret) > 0
                assert set(new_ret).issubset(self._unknown_regs)
                
                self._logger.dump('Registers added to retention list:')
                self._logger.dump('\n'.join(new_ret))

                ret_by_cex += new_ret
                self._ret_regs |= set(new_ret)
                self._unknown_regs -= set(new_ret)
            else:
                self._logger.dump('Error: Failed to prove property within {}s.'.format(Config.DEFAULT_VERIF_TIMEOUT))
                self._logger.dump('The registers in the retention list are necessary but may not be sufficient.')
                self._logger.dump('Exitting...')
                break

            # record the solution
            self._dst.take_screenshot(self._ret_regs, self._non_ret_regs, self._unknown_regs, {'ret_by_cex': ret_by_cex})

            # Check for timeout
            if self._timer.get_elapsed_time() > Config.DEFAULT_TIMEOUT:
                self._logger.dump('Timeout: Solving time ({}s) is larger than {}s.'.format(self._timer.get_elapsed_time(), Config.DEFAULT_TIMEOUT))
                self._logger.dump('Exitting...')
                break
        
        #assert not self._unknown_regs
        #assert self._regs == (self._ret_regs | self._non_ret_regs)

        # report solving information
        self._report_solving_info()

    
    def optimize_retention_list(self):
        """ Analyze the registers in self._unknown_regs and put them into self._ret_regs/self._non_ret_regs """
        """ Algorithm: set exploration combined with CEX-guided approach """
        ### Recommended use case: minimize the number of retention registers from a complete retention list ###

        target_regs = self._get_target_regs()
        while target_regs:
            # record current progress
            self._report_current_progress()
            self._logger.dump('Check registers:')
            self._logger.dump('\n'.join(target_regs))

            # create proof script for Jasper
            with open(self._retention_checker, 'r') as fr:
                ret_checker = [ line.strip('\n') for line in fr.readlines() ]
            
            ret_checker += self._gen_trace_info_getter_2(target_regs)
            ret_checker += ['exit']

            # generate partial retention design
            r_noret = self._non_ret_regs | target_regs
            self._gen_partret_design(r_noret)

            # launch Jasper
            out_msg = self._solver._exec_jg(ret_checker)
            #self._logger.dump(out_msg)

            # parse Jasper output
            res = self._solver._parse_jg_result(out_msg)
            self._logger.dump(res)

            # update timing information
            self._timer.update_time(res['output_equiv'])
            
            if JasperSolver.is_proven(res):
                self._non_ret_regs |= target_regs
            elif JasperSolver.is_cex(res):
                if len(target_regs) == 1:
                    self._ret_regs |= target_regs
                else:
                    # extract cex trace info
                    input_vals = self._solver.extract_cex_trace_info(out_msg, list(self._input_width_list.keys()) + ['pr_restore'])
                    check_cond_vals = self._solver.extract_cex_trace_info(out_msg, ['check_cond'])['check_cond']

                    # create simulation testbench
                    self._gen_wrapper_sim_2([check_cond_vals, input_vals]) # TODO: allow customized assertions

                    ret_candids = self._solver.get_retention_candidates(out_msg)
                    assert len(ret_candids) > 0

                    # Print the candidate retention registers
                    if self._verbosity > 0:
                        self._logger.dump('Retention candidates:')
                        self._logger.dump('\n'.join(ret_candids))
                    
                    new_ret = []
                    while len(ret_candids) > 0:
                        candid = ret_candids.pop()

                        # generate partial retention design
                        # TODO: for simulation, create a large power-collapsible design instead?
                        r_noret = self._non_ret_regs | (target_regs - set(new_ret + ret_candids))
                        self._gen_partret_design(r_noret)

                        # simulate
                        sim_msg = self._simulator.exec()
                        
                        # extend retention list
                        if IcarusSolver.is_cex(sim_msg):
                            new_ret.append(candid)

                    assert len(new_ret) > 0
                    
                    self._logger.dump('Registers added to retention list:')
                    self._logger.dump('\n'.join(new_ret))

                    self._ret_regs |= set(new_ret)
            else:
                self._logger.dump('Error: Failed to prove property within {}s.'.format(Config.DEFAULT_VERIF_TIMEOUT))
                self._logger.dump('The registers in the retention list are sufficient but may not be necessary.')
                self._logger.dump('Exitting...')
                break
            
            self._unknown_regs -= (self._ret_regs | self._non_ret_regs)
            target_regs = self._get_target_regs()

            # record the current solution
            self._dst.take_screenshot(self._ret_regs, self._non_ret_regs, self._unknown_regs)

            # Check for timeout
            if self._timer.get_elapsed_time() > Config.DEFAULT_TIMEOUT:
                self._logger.dump('Timeout: Solving time ({}s) is larger than {}s.'.format(self._timer.get_elapsed_time(), Config.DEFAULT_TIMEOUT))
                self._logger.dump('Exitting...')
                break

        #assert not self._unknown_regs
        #assert self._regs == (self._ret_regs | self._non_ret_regs)

        # report solving information
        self._report_solving_info()

    
    def _gen_wrapper_sim_2(self, trace_info):
        """ Wrap up the original and power-collapsible designs (for simulation) """
        
        # Target content
        # - wrapper_sim.sv
        wrapper = os.path.join(self._workdir, 'wrapper_sim.sv')

        sig_declare_list = []

        assignment_list = []

        golden_port_list = []
        test_port_list = []

        # clocks
        sig_declare_list.append('reg {} = 1;'.format(self._clock))
        golden_port_list.append('    .{}({}),'.format(self._clock, self._clock))
        test_port_list.append('    .{}({}),'.format(self._clock, self._clock))

        for clk in self._secondary_clocks:
            sig_declare_list.append('reg {} = 0;'.format(clk))  # TODO: What if there are multiple fastest clocks?
            
            golden_port_list.append('    .{}({}),'.format(clk, clk))
            test_port_list.append('    .{}({}),'.format(clk, clk))
        
        # resets
        for reset, val in self._resets.items():
            sig_declare_list.append('reg {} = {};'.format(reset, 1 - val))
            
            golden_port_list.append('    .{}({}),'.format(reset, reset))
            test_port_list.append('    .{}({}),'.format(reset, reset))
        
        # input ports
        for input, width in self._input_width_list.items():
            if input in self._reset_input_vals:
                sig_declare_list.append('reg [{}:0] {} = {};'.format(width - 1, input, self._reset_input_vals[input]))
            else:
                sig_declare_list.append('reg [{}:0] {};'.format(width - 1, input))
            
            golden_port_list.append('    .{}({}),'.format(input, input))
            test_port_list.append('    .{}({}),'.format(input, input))
        
        # output ports
        for output, width in self._output_width_list.items():
            sig_declare_list.append('wire [{}:0] {}, {}_test;'.format(width - 1, output, output))
            golden_port_list.append('    .{}({}),'.format(output, output))
            test_port_list  .append('    .{}({}_test),'.format(output, output))

        # Remove the last comma in the port lists
        golden_port_list[-1] = golden_port_list[-1][:-1]
        #test_port_list[-1] = test_port_list[-1][:-1]
        
        # pr_restore
        sig_declare_list.append('reg pr_restore = 0;')
        test_port_list.append('    .pr_restore(pr_restore)')

        # module instantiation
        # TODO: automatically determine top module?
        golden_inst = ['{} design_golden ('.format(self._top_module)] + golden_port_list + [');']
        test_inst = ['{}_test design_test ('.format(self._top_module)] + test_port_list + [');']

        lines = []
        
        #lines += ['`timescale 1ns / 1ps', '', 'module wrapper;', '']
        lines += ['module wrapper;', '']
        lines += sig_declare_list + ['']
        lines += assignment_list + ['']
        lines += golden_inst +  [''] + test_inst + ['']

        lines += ['// Simulation testbench', ''] + self._gen_testbench_2(trace_info) + ['']

        lines += ['endmodule']

        with open(wrapper, 'w') as fw:
            print('\n'.join(lines), file=fw)
    
    def _gen_wrapper_sim(self, trace_info):
        """ Wrap up the original and power-collapsible designs (for simulation) """
        
        # Target content
        # - wrapper_sim.sv
        wrapper = os.path.join(self._workdir, 'wrapper_sim.sv')

        sig_declare_list = []

        assignment_list = []

        golden_port_list = []
        test_port_list = []

        # clock and reset
        sig_declare_list += [
            'reg {} = 1;'.format(self._clock),
            #'reg {} = 0;'.format(self._reset)
        ]
        
        golden_port_list += [
            '    .{}({}),'.format(self._clock, self._clock),
            #'    .{}({}),'.format(self._reset, self._reset)
        ]
        test_port_list += [
            '    .{}({}),'.format(self._clock, self._clock),
            #'    .{}({}),'.format(self._reset, self._reset)
        ]

        for clk in self._secondary_clocks:
            sig_declare_list.append('reg {} = 0;'.format(clk))
            
            golden_port_list.append('    .{}({}),'.format(clk, clk))
            test_port_list.append('    .{}({}),'.format(clk, clk))
        
        # resets
        for reset, val in self._resets.items():
            sig_declare_list.append('reg {} = {};'.format(reset, 1 - val))
            
            golden_port_list.append('    .{}({}),'.format(reset, reset))
            test_port_list.append('    .{}({}),'.format(reset, reset))
        
        # input ports
        for input, width in self._input_width_list.items():
            if input in self._reset_input_vals:
                sig_declare_list.append('reg [{}:0] {} = {};'.format(width - 1, input, self._reset_input_vals[input]))
            else:
                sig_declare_list.append('reg [{}:0] {};'.format(width - 1, input))
            
            golden_port_list.append('    .{}({}),'.format(input, input))
            test_port_list.append('    .{}({}),'.format(input, input))
        
        # output ports
        for output, width in self._output_width_list.items():
            sig_declare_list.append('wire [{}:0] {}, {}_test;'.format(width - 1, output, output))
            golden_port_list.append('    .{}({}),'.format(output, output))
            test_port_list  .append('    .{}({}_test),'.format(output, output))

        # Remove the last comma in the port lists
        golden_port_list[-1] = golden_port_list[-1][:-1]
        #test_port_list[-1] = test_port_list[-1][:-1]
        
        # pr_restore
        sig_declare_list.append('reg pr_restore = 0;')
        test_port_list.append('    .pr_restore(pr_restore)')

        # module instantiation
        # TODO: automatically determine top module?
        golden_inst = ['{} design_golden ('.format(self._top_module)] + golden_port_list + [');']
        test_inst = ['{}_test design_test ('.format(self._top_module)] + test_port_list + [');']

        lines = []
        
        #lines += ['`timescale 1ns / 1ps', '', 'module wrapper;', '']
        lines += ['module wrapper;', '']
        lines += sig_declare_list + ['']
        lines += assignment_list + ['']
        lines += golden_inst +  [''] + test_inst + ['']

        lines += ['// Simulation testbench', ''] + self._gen_testbench(trace_info) + ['']

        lines += ['endmodule']

        with open(wrapper, 'w') as fw:
            print('\n'.join(lines), file=fw)

    
    def _gen_testbench_2(self, trace_info: list) -> list:
        """ Create simulation testbench based on the counterexample trace """

        check_cond_vals = trace_info[0]
        input_vals = trace_info[1]

        # Debug
        #self._logger.dump('check_cond_vals: {}'.format(check_cond_vals))
        #self._logger.dump('input_vals: {}'.format(input_vals))
        
        clk_progress = [ 'always #5 {} = ~{};'.format(self._clock, self._clock) ]

        max_factor = 1
        for clk, factor in self._secondary_clocks.items():
            clk_progress += [ 'always #{} {} = ~{};'.format(5 * factor, clk, clk) ]
            max_factor = max(max_factor, factor)
        
        clk_progress += [ '' ]

        # initialize non-resettable registers
        init = [ '// Initialize all non-resettable registers to 0' ]
        for reg in self._non_resettable_regs:
            reg_renamed = YosysSolver.rename_to_test_sig(reg)
            init += [
                'design_golden.{} = 0;'.format(reg),
                'design_test.{} = 0;'.format(reg_renamed)
            ]
        init += [ '' ]
        
        cycles = [
            '// Reset',
            '#1;',
            #'{} = 1\'b1;'.format(self._reset),
            ' '.join([ '{} = {};'.format(reset, val) for reset, val in self._resets.items() ]),
            'repeat ({}) @(posedge {});'.format(10 * max_factor, self._clock),  # TODO: config reset cycles
            #'#1;',
            #'{} = 1\'b0;'.format(self._reset),
            ''
        ]

        out_diff = ' | '.join(['({} != {}_test)'.format(out, out) for out in self._output_width_list.keys()])
        pow_out_diff = ' | '.join(['({} != {}_test)'.format(out, out) for out in self._power_outputs])
        
        trace_len = len(check_cond_vals)
        for i in range(trace_len):
            cycle = [
                '// Cycle {}'.format(i+1),
                '#1;'
            ]

            if i == 0:
                cycle += [
                    '',
                    '// End reset',
                    #'{} = 1\'b0;'.format(self._reset),
                    ' '.join([ '{} = {};'.format(reset, 1 - val) for reset, val in self._resets.items() ]),
                    ''
                ]
                cycle += init
            
            for input in input_vals:
                cycle.append('{} = {};'.format(input, input_vals[input][i]))
            
            cycle += [
                '',
                '@(negedge {});'.format(self._clock),
                #'$display("cycle {}");'.format(i+1),
                'if ({}) begin'.format( pow_out_diff if (check_cond_vals[i] == '1\'b0') else out_diff ),
                #'if ({}) begin'.format( out_diff ),
                '    $display("cex");',
                #'    $display("cex{}");'.format(i+1),
                '    $finish;',
                'end',
                '',
                '@(posedge {});'.format(self._clock),
                ''
            ]
            
            cycles += cycle
        
        cycles += [
            '// Done',
            '$display("proven");',
            '$finish;'
        ]

        trace = ['initial begin'] + ['    {}'.format(line) for line in cycles] + ['end']

        return clk_progress + trace
    
    def _gen_testbench(self, trace_info: list) -> list:
        """ Create simulation testbench based on the counterexample trace """

        check_cond_vals = trace_info[0]
        input_vals = trace_info[1]

        # Debug
        #self._logger.dump('check_cond_vals: {}'.format(check_cond_vals))
        #self._logger.dump('input_vals: {}'.format(input_vals))
        
        clk_progress = [ 'always #5 {} = ~{};'.format(self._clock, self._clock) ]

        max_factor = 1
        for clk, factor in self._secondary_clocks.items():
            clk_progress += [ 'always #{} {} = ~{};'.format(5 * factor, clk, clk) ]
            max_factor = max(max_factor, factor)
        
        clk_progress += [ '' ]

        # initialize non-resettable registers
        init = [ '// Initialize all non-resettable registers to 0' ]
        for reg in self._non_resettable_regs:
            reg_renamed = YosysSolver.rename_to_test_sig(reg)
            init += [
                'design_golden.{} = 0;'.format(reg),
                'design_test.{} = 0;'.format(reg_renamed)
            ]
        init += [ '' ]
        
        cycles = [
            '// Reset',
            '#1;',
            #'{} = 1\'b1;'.format(self._reset),
            ' '.join([ '{} = {};'.format(reset, val) for reset, val in self._resets.items() ]),
            'repeat ({}) @(posedge {});'.format(10 * max_factor, self._clock),  # TODO: config reset cycles
            #'#1;',
            #'{} = 1\'b0;'.format(self._reset),
            ''
        ]

        out_diff = ' | '.join(['({} != {}_test)'.format(out, out) for out in self._output_width_list.keys()])
        pow_out_diff = ' | '.join(['({} != {}_test)'.format(out, out) for out in self._power_outputs])
        
        trace_len = len(check_cond_vals)
        for i in range(trace_len):
            cycle = [
                '// Cycle {}'.format(i+1),
                '#1;'
            ]

            if i == 0:
                cycle += [
                    '',
                    '// End reset',
                    #'{} = 1\'b0;'.format(self._reset),
                    ' '.join([ '{} = {};'.format(reset, 1 - val) for reset, val in self._resets.items() ]),
                    ''
                ]
                cycle += init
            
            for input in input_vals:
                cycle.append('{} = {};'.format(input, input_vals[input][i]))
            
            cycle += [
                '',
                '@(negedge {});'.format(self._clock),
                #'$display("cycle {}");'.format(i+1),
                'if ({}) begin'.format( pow_out_diff if (check_cond_vals[i] == '1\'b0') else out_diff ),
                #'if ({}) begin'.format( out_diff ),
                '    $display("cex");',
                #'    $display("cex{}");'.format(i+1),
                '    $finish;',
                'end',
                '',
                '@(posedge {});'.format(self._clock),
                ''
            ]
            
            cycles += cycle
        
        cycles += [
            '// Done',
            '$display("proven");',
            '$finish;'
        ]

        trace = ['initial begin'] + ['    {}'.format(line) for line in cycles] + ['end']

        return clk_progress + trace
    
    
    def _get_target_regs(self):
        """ Returns a batch (set) of target registers for the next retention check """
        
        # initialize register batches if not already
        if self._reg_batches is None:
            #b_neighbor = [frozenset(self._get_regs_of_same_module(r, self._unknown_regs)) for r in self._unknown_regs]
            b_neighbor = self._group_regs_of_same_instance(self._unknown_regs)

            b_friend = [frozenset(self._get_regs_with_similar_names(r, self._unknown_regs)) for r in self._unknown_regs]

            b_same_suffix = [frozenset(self._get_regs_with_same_suffix(r, self._unknown_regs)) for r in self._unknown_regs]
            
            b_copy = [frozenset(self._get_copied_regs(r, self._unknown_regs)) for r in self._unknown_regs]
            b_raw = [frozenset([r]) for r in self._unknown_regs]

            #b_all = set(b_neighbor) | set(b_friend) | set(b_copy) | set(b_raw)
            b_all = set(b_neighbor) | set(b_friend) | set(b_same_suffix) | set(b_copy) | set(b_raw)
        
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

    
    def _gen_trace_info_getter_2(self, candid_regs: list) -> list:
        """ Generate the Jasper commands to extract trace info when the assertion fails """

        cmds = [
            'set result [get_property_info output_equiv -list status]',
            'if { $result != "cex" } {',
            '   exit',
            '}',
            'visualize -violation -property output_equiv',
            ''
        ]
    
        # Report trace info
        for input in self._input_width_list:
            cmds.append('visualize -get_value {} -radix 2'.format(input))
        cmds.append('visualize -get_value pr_restore -radix 2')

        cmds.append('visualize -get_value check_cond -radix 2')

        # Print the candidate retention registers
        cmds += [
            '',
            'set restore [visualize -get_value pr_restore -radix 2]',
            'set indices [list]',
            'for {set i 1} {$i < [llength $restore]} {incr i} {',
            '    set prev [lindex $restore [expr $i - 1]]',
            '    if { $prev == "1\'b1" } {',
            '        lappend indices $i',
            '    }',
            '}',
            '',
            #'set reglist [ get_design_info -instance design_golden -list register ]',
            'set reglist {{ {} }}'.format(' '.join(candid_regs)),
            '',
            'set candid_regs [list]',
            'for {set i 0} {$i < [llength $indices]} {incr i} {',
            '    set cycle [expr [lindex $indices $i] + 1]',
            '    foreach reg $reglist {',
            #'        # remove "design_golden."',
            #'        set reg [string range $reg 14 end]',
            '        if { [string first "." $reg] != -1 } {',
            '            set reg_test "\\\\$reg"',
            '        } else {',
            '            set reg_test $reg',
            '        }',
            '',
            '        set golden_val [ visualize -get_value design_golden.$reg $cycle -radix 2 ]',
            '        set test_val [ visualize -get_value design_test.$reg_test $cycle -radix 2 ]',
            '        if { $golden_val != $test_val } {',
            '            lappend candid_regs $reg',
            '        }',
            '    }',
            '}',
            '',
            'puts $candid_regs',
            ''
        ]

        return cmds
    

    def _gen_trace_info_getter(self) -> list:
        """ Generate the Jasper commands to extract trace info when the assertion fails """

        cmds = [
            'set result [get_property_info output_equiv -list status]',
            'if { $result != "cex" } {',
            '   exit',
            '}',
            'visualize -violation -property output_equiv',
            ''
        ]
    
        for input in self._input_width_list:
            cmds.append('visualize -get_value {} -radix 2'.format(input))
        cmds.append('visualize -get_value pr_restore -radix 2')

        cmds.append('visualize -get_value check_cond -radix 2')

        # Print the candidate retention registers
        cmds += [
            '',
            'set restore [visualize -get_value pr_restore -radix 2]',
            'set indices [list]',
            'for {set i 1} {$i < [llength $restore]} {incr i} {',
            '    set prev [lindex $restore [expr $i - 1]]',
            '    if { $prev == "1\'b1" } {',
            '        lappend indices $i',
            '    }',
            '}',
            '',
            'set reglist [ get_design_info -instance design_golden -list register ]',
            '',
            'set candid_regs [list]',
            'for {set i 0} {$i < [llength $indices]} {incr i} {',
            '    set cycle [expr [lindex $indices $i] + 1]',
            '    foreach reg $reglist {',
            '        # remove "design_golden."',
            '        set reg [string range $reg 14 end]',
            '        if { [string first "." $reg] != -1 } {',
            '            set reg_test "\\\\$reg"',
            '        } else {',
            '            set reg_test $reg',
            '        }',
            '',
            '        set golden_val [ visualize -get_value design_golden.$reg $cycle -radix 2 ]',
            '        set test_val [ visualize -get_value design_test.$reg_test $cycle -radix 2 ]',
            '        if { $golden_val != $test_val } {',
            '            lappend candid_regs $reg',
            '        }',
            '    }',
            '}',
            '',
            'puts $candid_regs',
            ''
        ]

        return cmds
    

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
    
    def _group_regs_of_same_instance(self, pool, length=0):
        """ Group registers that are in the same instance """
        
        root_inst = []
        other_insts = {}

        for reg in pool:
            if reg.count('.') == length:
                root_inst.append(reg)
            else:
                inst_of_reg = reg.split('.')[length]
                if inst_of_reg not in other_insts:
                    other_insts[inst_of_reg] = [reg]
                else:
                    other_insts[inst_of_reg].append(reg)

        if not other_insts:
            return []
        else:
            return [frozenset(root_inst)] + [frozenset(grp) for grp in other_insts.values()] \
                + list(itertools.chain.from_iterable([self._group_regs_of_same_instance(grp, length + 1) for grp in other_insts.values()]))
    
#    def _get_regs_with_similar_names(self, target, pool):
#        """ Get the regs that have similar names as the target """
#
#        def _diff_in_digits(a, b):
#            """ Differ only in digits """
#
#            def _remove_digits(in_str):
#                return ''.join([c for c in in_str if not (c.isdigit())])
#
#            return _remove_digits(a) == _remove_digits(b)
#
#        def _diff_in_suffix(a, b):
#            """ Differ only in the last suffix """
#
#            return (a.split('_')[:-1] == b.split('_')[:-1]) if '_' in a else False
#
#        def _is_similar(a, b):
#            """ Compare tails of two paths """
#
#            tail_a = a.split('.')[-1]
#            tail_b = b.split('.')[-1]
#
#            return _diff_in_digits(
#                tail_a, tail_b) or _diff_in_suffix(tail_a, tail_b)
#
#        return [reg for reg in pool if _is_similar(target, reg)]
    
    
    def _get_regs_with_similar_names(self, target, pool):
        """ Get the regs that have similar names as the target """

        def _diff_in_digits(a, b):
            """ Differ only in digits """

            def _remove_digits(in_str):
                #return ''.join([c for c in in_str if not (c.isdigit())])
                return ''.join([c for c in in_str if not (c.isdigit() or c == '_')])

            return _remove_digits(a) == _remove_digits(b)

        def _diff_in_suffix(a, b):
            """ Differ only in the last suffix """

            #return (a.split('_')[:-1] == b.split('_')[:-1]) if '_' in a else False

            a_parts = a.split('_')
            b_parts = b.split('_')

            if len(a_parts) < len(b_parts):
                return a_parts == b_parts[:len(a_parts)]
            #elif len(a_parts) > len(b_parts):
            #    return a_parts[:len(b_parts)] == b_parts
            elif len(a_parts) == len(b_parts) and len(a_parts) > 1:
                return a_parts[:-1] == b_parts[:-1]
            else:
                return False

        def _is_similar(a, b):
            """ Compare tails of two paths """

            tail_a = a.split('.')[-1]
            tail_b = b.split('.')[-1]

            return _diff_in_digits(
                tail_a, tail_b) or _diff_in_suffix(tail_a, tail_b)

        return [reg for reg in pool if _is_similar(target, reg)]
    
    def _get_regs_with_same_suffix(self, target, pool):
        """ Get the regs that have the same suffix as the target """

        def _is_same_suffix(a, b):
            """ Compare two paths to check if is of a same suffix """

            # same length and only diff at the tail
            return a.split('_')[0] == b.split('_')[0]
        
        return [reg for reg in pool if _is_same_suffix(target.split('.')[-1], reg.split('.')[-1])]
    
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

        self._timer.start_iteration()

    def _report_solving_info(self):
        """ Report the final result """

        self._logger.fence()
        self._logger.dump('Summary ({}):'.format(datetime.now()))
        
        def _get_bit_count(regs: set) -> int:
            """ Get the total bit count of the registers """

            return sum([int(self._regs_and_resets[reg].split("'")[0]) for reg in regs])
        
        reg_total = len(self._regs)
        bit_total = _get_bit_count(self._regs)
        
        def _get_info(regs: set) -> list:
            
            reg_count = len(regs)
            bit_count = _get_bit_count(regs)
            
            reg_percent = (float(reg_count) / reg_total) * 100
            bit_percent = (float(bit_count) / bit_total) * 100
            
            return [reg_count, bit_count, reg_percent, bit_percent]
        
        ret_info = _get_info(self._ret_regs)
        non_ret_info = _get_info(self._non_ret_regs)
        unknown_info = _get_info(self._unknown_regs)
        
        self._logger.dump('#retention:     {}/{} ({}% / {}%)'.format(ret_info[0], ret_info[1], format(ret_info[2], '.2f'), format(ret_info[3], '.2f')))
        self._logger.dump('#non retention: {}/{} ({}% / {}%)'.format(non_ret_info[0], non_ret_info[1], format(non_ret_info[2], '.2f'), format(non_ret_info[3], '.2f')))
        self._logger.dump('#unknown:       {}/{} ({}% / {}%)'.format(unknown_info[0], unknown_info[1], format(unknown_info[2], '.2f'), format(unknown_info[3], '.2f')))
        
        self._logger.dump('Iterations: {}'.format(self._timer.get_iterations()))
        self._logger.dump('  Proven: {}, CEX: {}'.format(self._timer.get_pf_rounds(), self._timer.get_cex_rounds()))
        self._logger.dump('Solving time: {}'.format(self._timer.get_elapsed_time()))
        self._logger.dump('Average proof time: {}'.format(self._timer.get_avg_pf_time()))
        self._logger.dump('Average CEX time:   {}'.format(self._timer.get_avg_cex_time()))
    
    