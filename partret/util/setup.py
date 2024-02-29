#!/usr/bin/env python3

# TODO: license

import json
import os

from partret.checker.checker import Checker
from partret.config import Config

class Setup(Checker):
    """ Set up the proof environment for the partial retention check """
    
    def __init__(self, config, logger, workdir, verbosity=0):
        """ Constructor """
        
        super().__init__(config, logger, workdir, verbosity)

        self._run()

    
    def _run(self):
        # Note: this function was already called in the constructor
        #self._get_design_info()
        
        self._gen_partret_design()

        # sanity check
        self._get_design_info('_test')

        self._gen_wrapper()
        
        self._gen_ret_checker()
        
        if self._verbosity == 0:
            os.rmdir(self._tmpdir)

    
    def _get_design_info(self, sub=''):
        """ Get design information (requires Jasper) """

        self._logger.dump('\n'.join([
            '========================================',
            'Generating design information (design{}_info.json) ...'.format(sub),
            ''
        ]))

        # Require
        # - RTL files
        # - (top module)
        # - clock and reset information

        # Temporary files
        # - get input list
        # - get output list
        # - get register list
        # - get reset values list
        input_list = os.path.join(self._tmpdir, 'input_list{}.txt'.format(sub))
        output_list = os.path.join(self._tmpdir, 'output_list{}.txt'.format(sub))
        register_list = os.path.join(self._tmpdir, 'register_list{}.txt'.format(sub))
        reset_values = os.path.join(self._tmpdir, 'reset_values{}.txt'.format(sub))

        # Target content
        # - design_info.json
        design_info = os.path.join(self._workdir, 'design{}_info.json'.format(sub))
        
        cmds = []

        # analyze and elaborate the design
        if sub == '_test':
            design_files = [os.path.join(self._workdir, 'design_test.v')]
        else:
            design_files = self._get_design_files()
        
        for file in design_files:
            cmds.append('analyze -sv {}'.format(file))
        
        if self._top_module:
            cmds.append('elaborate -top {}{}'.format(self._top_module, sub))
        else:
            cmds.append('elaborate')
        
        # source clock and reset information
        cmds.append('clock {}'.format(self._clock))

        for clk, factor in self._secondary_clocks.items():
            cmds.append('clock {} -factor {}'.format(clk, factor))
        
        cmds.append('reset {} -non_resettable_regs 0'.format(self._reset))

        # Assumptions during reset
        for input, val in self._reset_input_vals.items():
            cmds.append('assume -reset {{ {} == {} }}'.format(input, val))
        cmds.append('')
        
        # collect design information
        cmds += [
            'get_reset_info -all -save_values {}'.format(reset_values),

            'get_design_info -list input -file {} -force'.format(input_list),
            'get_design_info -list output -file {} -force'.format(output_list),

            'get_design_info -list register -file {} -force'.format(register_list),

            'exit'
        ]

        if self._verbosity > 0:
            # dump Jasper script
            with open(os.path.join(self._tmpdir, 'get_design{}_info.tcl'.format(sub)), 'w') as fw:
                print('\n'.join(cmds), file=fw)
        
        # lauch Jasper
        self._solver._exec_jg(cmds)

        def get_signal_width(f):
            with open(f, 'r') as fr:
                data = [x.strip() for x in list(fr)[2:]]
                signals = [x.split()[0] for x in data if x]
                widths = [int(x.split()[1].strip('()')) for x in data if x]
                signal_widths = dict(zip(signals, widths))
            return signal_widths
        
        # input list
        input_widths = get_signal_width(input_list)

        # output list
        output_widths = get_signal_width(output_list)
        
        # register list # TODO: no need for this?
        reg_widths = get_signal_width(register_list)

        # register reset values
        with open(reset_values, 'r') as fr:
            data = [x.strip() for x in list(fr)]
            reg_resets = dict(zip(data[0::2], data[1::2]))
        
        with open(design_info, 'w') as fw:
            info = {
                'input_list': input_widths,
                'output_list': output_widths,
                'register_list': reg_widths,
                'reset_values': reg_resets
            }
            json.dump(info, fw, indent=4)

        if self._verbosity == 0:
            os.remove(input_list)
            os.remove(output_list)
            os.remove(register_list)
            os.remove(reset_values)
        
        self._logger.dump('\n'.join([
            '',
            'Done.'
        ]))


    def _gen_partret_design(self):
        ### Generate a partial retention design (requires Yosys) ###

        self._logger.dump('\n'.join([
            '========================================',
            'Generating partial retention design (design_test.v) ...',
            ''
        ]))

        if self._unknown_regs:
            self._logger.dump('Warning: The registers in the unknown set are treated as retention registers.')

        super()._gen_partret_design(self._non_ret_regs)

        self._logger.dump('\n'.join([
            '',
            'Done.'
        ]))
    

    def _gen_power_design(self):
        """ Generate power-collapsible design (requires Yosys) """
        
        self._logger.dump('\n'.join([
            '========================================',
            'Generating power-collapsible design (design_test.v) ...',
            ''
        ]))

        # Require
        # - RTL files
        # - (top module)
        # - reset_values.txt: reset values for all registers (generated by _get_design_info())
        reset_values = os.path.join(self._tmpdir, 'reset_values.txt')

        # Target content
        # - design_test.v: power-collapsible design
        design_test = os.path.join(self._workdir, 'design_test.v')

        cmds = []

        # read Verilog files
        design_files = self._get_design_files()
        for file in design_files:
            cmds.append('read_verilog -mem2reg {}'.format(file))   # TODO: mem2reg?
        
        if self._top_module:
            cmds.append('hierarchy -check -top {}'.format(self._top_module))
        else:
            cmds.append('hierarchy -check -auto-top')
        
        # generate power-collapsible design
        cmds += [
            'proc',
            'flatten',
            #'opt_clean',    # TODO: modify the original design instead?

            'make_power_collapsible -reset_vals {}'.format(reset_values),

            'rename -top {}_test'.format(self._top_module),

            'write_verilog -nodec -noattr -noparallelcase {}'.format(design_test)
        ]

        if self._verbosity > 0:
            # dump Yosys script
            with open(os.path.join(self._tmpdir, 'gen_design_test.ys'), 'w') as fw:
                print('\n'.join(cmds), file=fw)
        
        # lauch Yosys
        self._ys_solver._exec_yosys(cmds)

        if self._verbosity == 0:
            os.remove(reset_values)

        self._logger.dump('\n'.join([
            '',
            'Done.'
        ]))


    def _gen_wrapper(self):
        """ Wrap up the original and power-collapsible designs """

        self._logger.dump('\n'.join([
            '========================================',
            'Generating wrapper (wrapper.sv) ...',
            ''
        ]))

        # Target content
        # - wrapper.sv
        wrapper = os.path.join(self._workdir, 'wrapper.sv')
        
        sig_declare_list = []

        assignment_list = []

        golden_port_list = []
        test_port_list = []
        
        # clock and reset
        sig_declare_list += [
            'wire {};'.format(self._clock),
            'wire {};'.format(self._reset)
        ]
        
        golden_port_list += [
            '    .{}({}),'.format(self._clock, self._clock),
            '    .{}({}),'.format(self._reset, self._reset)
        ]
        test_port_list += [
            '    .{}({}),'.format(self._clock, self._clock),
            '    .{}({}),'.format(self._reset, self._reset)
        ]

        for clk in self._secondary_clocks:
            sig_declare_list.append('wire {};'.format(clk))
            
            golden_port_list.append('    .{}({}),'.format(clk, clk))
            test_port_list.append('    .{}({}),'.format(clk, clk))
        
        # input ports
        for input, width in self._input_width_list.items():
            sig_declare_list.append('wire [{}:0] {};'.format(width - 1, input))
            
            golden_port_list.append('    .{}({}),'.format(input, input))
            test_port_list.append('    .{}({}),'.format(input, input))
        
        # output ports
        for output, width in self._output_width_list.items():
            sig_declare_list.append('wire [{}:0] {}, {}_test;'.format(width - 1, output, output))
            golden_port_list.append('    .{}({}),'.format(output, output))
            test_port_list  .append('    .{}({}_test),'.format(output, output))

        # check condition
        # Note: This is required for the complete algorithm
        sig_declare_list.append('wire check_cond;')
        assignment_list.append('assign check_cond = {};'.format(self._check_cond))

        # Remove the last comma in the port lists
        golden_port_list[-1] = golden_port_list[-1][:-1]
        #test_port_list[-1] = test_port_list[-1][:-1]
        test_port_list.append('    .pr_restore(pr_restore)')

        # module instantiation
        # TODO: automatically determine top module?
        golden_inst = ['{} design_golden ('.format(self._top_module)] + golden_port_list + [');']
        test_inst = ['{}_test design_test ('.format(self._top_module)] + test_port_list + [');']

        lines = [
            '// This is the testbench that wraps the original and partial retention designs.',
            '// This script will be used by the retention explorer tool, ',
            '// so please (only) modify it as instructed (marked with "// TODO: ...") if you want to call the explorer.',
            ''
        ]
        
        lines += ['module wrapper;', '']
        lines += sig_declare_list + ['']
        lines += assignment_list + ['']
        lines += golden_inst +  [''] + test_inst + ['']
        lines += [
            '// TODO: Please add the formal interface constraints either here or in ret_checker.tcl.',
            '',
            ''
        ]
        
        lines += ['endmodule']

        with open(wrapper, 'w') as fw:
            print('\n'.join(lines), file=fw)
        
        self._logger.dump('\n'.join([
            '',
            'Done.'
        ]))


    def _gen_ret_checker(self):
        ### Generate the retention checker proof script (in Jasper format) ###
        
        self._logger.dump('\n'.join([
            '========================================',
            'Generating Jasper proof script (ret_checker.tcl) ...',
            ''
        ]))

        # Require
        # - design files
        # - clock and reset information
        # - power interface outputs
        # - check condition

        # Target content
        # - ret_checker.tcl: proof script for the partial retention check
        ret_checker = os.path.join(self._workdir, 'ret_checker.tcl')
        
        cmds = [
            '# This is the Jasper script for the self composition check.',
            '# This script would be used by the retention explorer tool, ',
            '# so please only modify it as instructed (marked with "# TODO: ...") if you want to call the explorer.',
            ''
        ]

        # 1. Set up the design
        design_files = self._get_design_files()
        for file in design_files:
            cmds.append('analyze -sv {}'.format(file))
        
        cmds += [
            'analyze -sv {}'.format(os.path.join(self._workdir, 'design_test.v')),
            'analyze -sv {}'.format(os.path.join(self._workdir, 'wrapper.sv')),
            '',
            'elaborate -top wrapper',
            ''
        ]

        # 2. Source clock and reset information
        cmds.append('clock {}'.format(self._clock))

        for clk, factor in self._secondary_clocks.items():
            cmds.append('clock {} -factor {}'.format(clk, factor))
        
        cmds.append('reset {} -non_resettable_regs 0'.format(self._reset))

        cmds += [
            '',
            '# TODO: You can configure the changing rate of inputs.',
            ''
        ]

        # Assumptions during reset
        for input, val in self._reset_input_vals.items():
            cmds.append('assume -reset {{ {} == {} }}'.format(input, val))
        cmds.append('')

        cmds += [
            '# TODO: Please add the formal interface constraints either here or in wrapper.sv.',
            '',
            ''
        ]

        # 4. Assertions
        power_out_equivs = [ '({} == {}_test)'.format(out, out) for out in self._power_outputs ]
        non_power_out_equivs = [ '({} == {}_test)'.format(out, out) for out in self._non_power_outputs ]

        cmds += [
            #'assert -disable {.*} -regexp',
            #'',
            '# TODO: You can modify the expression part of this assertion.',
            'assert -name output_equiv {{ @(posedge {}) disable iff ({})'.format(self._clock, self._reset),
            '    ( ' + ' &&\n    '.join(power_out_equivs) + ' ) &&',
            '    ( !({}) ||'.format(self._check_cond),
            '    ( ' + ' &&\n    '.join(non_power_out_equivs) + ' ) )',
            '}',
            ''
        ]

        # proof configuration
        cmds += [
            '# TODO: You can modify the proof settings.',
            #'set_engine_mode auto',
            'set_engine_mode {B Ht Mp}',
            #'set_proofgrid_per_engine_max_jobs 2',
            #'set_prove_per_property_time_limit 0s',
            #'set_prove_per_property_time_limit_factor 0',
            '',
            'set_prove_time_limit {}s'.format(Config.DEFAULT_TIMEOUT),
            ''
        ]

        # 5. Prove the properties
        # TODO: prove -save_ppd?
        #ppd = os.path.join(self._workdir, 'ret_checker.ppd')

        cmds += [
            #'prove -all -asserts',
            'prove -property output_equiv',
            #'prove -property {{ output_equiv }} -with_ppd {} -save_ppd {}'.format(ppd, ppd),
            ''
        ]

        # 6. Report the results
        cmds += [
            'get_property_info output_equiv -list status',
            'get_property_info output_equiv -list time',
            'get_property_info output_equiv -list engine',
            'get_property_info output_equiv -list trace_length',
            'get_property_info output_equiv -list proof_effort',
            'get_property_info output_equiv -list min_length',
            ''
        ]

        with open(ret_checker, 'w') as fw:
            print('\n'.join(cmds), file=fw)

        self._logger.dump('\n'.join([
            '',
            'Done.',
            '========================================',
        ]))
