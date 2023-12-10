#!/usr/bin/env python3

# TODO: license

import json
import os
import sys

from partret.config import Config
from partret.solver.jasper import JasperSolver
from partret.util.generic import rename_to_test_sig
#from partret.util.image import Image


class Checker:
    """ Partial retention checker """

    def __init__(self, config, logger, workdir, verbosity=0):
        """ constructor """
        
        self._logger = logger
        self._workdir = workdir
        self._verbosity = verbosity

        self._design_files = []

        self._clock = ""
        self._reset = ""
        self._top_module = ""

        self._standby_cond = ""
        self._check_cond = ""

        self._input_width_list = {}
        self._output_width_list = {}
        
        self._power_outputs = []
        self._non_power_outputs = []

        self._regs = set()
        self._ret_regs = set()
        self._non_ret_regs = set()
        self._unknown_regs = set()
        
        self._solver = JasperSolver(logger, workdir)
        
        self._setup(config)

        
    def _setup(self, config: dict):
        """ Set up checker based on the config file """

        # design files
        assert isinstance(config['RTL'], list)
        self._get_design_files(config['RTL'])

        # clock
        assert isinstance(config['clock'], str)
        self._clock = config['clock']

        # reset
        assert isinstance(config['reset'], str)
        self._reset = config['reset']

        # top module
        assert isinstance(config['top_module'], str)
        self._top_module = config['top_module']

        #if 'top_module' in config:
        #    assert isinstance(config['top_module'], str)
        #    self._top_module = config['top_module']
        #else:
        #    self._logger.dump('Warning: top_module is not specified in the config file.')
        
        # clock and reset information (for Jasper)
        self._clock_reset_info = config['clock_reset_info']
        assert os.path.isfile(self._clock_reset_info)
        
        # standby condition
        assert isinstance(config['standby_condition'], str)
        self._standby_cond = config['standby_condition']
        
        # check condition
        assert isinstance(config['check_condition'], str)
        self._check_cond = config['check_condition']

        # formal constraints
        assert os.path.isfile(config['formal_constraints'])
        with open(config['formal_constraints'], 'r') as fr:
            self._formal_constraints = fr.read().splitlines()

        # design information
        design_info = os.path.join(self._workdir, 'design_info.json')
        if not os.path.isfile(design_info):
            self._get_design_info()
        with open(design_info, 'r') as f:
            design_info = json.load(f)
        
        # input and output lists
        self._input_width_list = design_info['input_list']
        self._output_width_list = design_info['output_list']

        # power interface outputs
        assert isinstance(config['power_interface_outputs'], list)
        self._power_outputs = config['power_interface_outputs']
        self._non_power_outputs = list(set(design_info['output_list'].keys()) - set(self._power_outputs))

        # self._regs, self._ret_regs, self._non_ret_regs
        self._regs = set(design_info['register_list'].keys())

        assert os.path.isfile(config['src'])
        with open(config['src'], 'r') as f:
            src = json.load(f)

        def get_regs(reg_list: list) -> set:
            if reg_list == ['.']:
                regs = set(self._regs)
            else:
                regs = set(reg_list)
            return regs
        
        assert isinstance(src['retention'], list) & isinstance(src['non_retention'], list) & isinstance(src['unknown'], list)
        self._ret_regs = get_regs(src['retention'])
        self._non_ret_regs = get_regs(src['non_retention'])
        self._unknown_regs = get_regs(src['unknown'])

        self._check_reg_subsets()

    
    def _get_design_files(self, design_files=[]) -> list:
        """ Get design files """

        # initialize if not already
        if not self._design_files:

            def _append_design_files(file_or_dir):
                if os.path.isfile(file_or_dir):
                    self._design_files.append(file_or_dir)
                elif os.path.isdir(file_or_dir):
                    for sub_file_or_dir in os.listdir(file_or_dir):
                        _append_design_files(os.path.join(file_or_dir, sub_file_or_dir))
                else:
                    self._logger.dump('Error: {} is neither a file nor a directory!!!'.format(file_or_dir))
                    sys.exit(0)
            
            for file_or_dir in design_files:
                _append_design_files(file_or_dir)

        return self._design_files

    
    def _gen_wrapper(self, ret_list=None):
        """ Wrap up the original and power-collapsible designs """

        # Require
        # - top module
        # - input, output, and register lists (from design_info.json)
        # - standby condition
        # - interface constraints (in SVA)

        wire_declare_list = []

        assignment_list = []
        
        golden_port_list = []
        test_port_list = []

        # input ports
        for input, width in self._input_width_list.items():
            wire_declare_list.append('wire [{}:0] {};'.format(width - 1, input))
            golden_port_list.append('    .{}({}),'.format(input, input))
            test_port_list.append('    .{}({}),'.format(input, input))
        
        # output ports
        for output, width in self._output_width_list.items():
            wire_declare_list.append('wire [{}:0] {}, {}_test;'.format(width - 1, output, output))
            golden_port_list.append('    .{}({}),'.format(output, output))
            test_port_list  .append('    .{}({}_test),'.format(output, output))
        
        # partial retention
        for reg in self._regs:
            reg_renamed = rename_to_test_sig(reg)
            wire_declare_list.append('wire {}_ret;'.format(reg_renamed))
            test_port_list.append('    .{}_ret({}_ret),'.format(reg_renamed, reg_renamed))
            
            if ret_list is not None:
                if reg in ret_list:
                    assignment_list.append('assign {}_ret = 1\'b1;'.format(reg_renamed))
                else:
                    assignment_list.append('assign {}_ret = 1\'b0;'.format(reg_renamed))
        
        # standby condition
        wire_declare_list.append('wire standby_cond;')
        test_port_list.append('    .standby_cond(standby_cond),')
        assignment_list.append('assign standby_cond = {};'.format(self._standby_cond))

        # Remove the last comma in the port lists
        golden_port_list[-1] = golden_port_list[-1][:-1]
        test_port_list[-1] = test_port_list[-1][:-1]

        # TODO: formal verification or simulation?

        # module instantiation
        # TODO: automatically determine top module?
        golden_inst = ['{} design_golden ('.format(self._top_module)] + golden_port_list + [');']
        test_inst = ['{}_test design_test ('.format(self._top_module)] + test_port_list + [');']

        cmds = ['module wrapper;', '']
        cmds += wire_declare_list + ['']
        cmds += assignment_list + ['']
        cmds += golden_inst +  [''] + test_inst + ['']
        cmds += ['// Formal constraints', ''] + self._formal_constraints + ['']
        cmds += ['endmodule']

        return cmds

    
    def _gen_ret_checker(self, ret_list=None):
        """ Generate a proof script (ret_checker.tcl) for the target retention list """

        # Require
        # - design files
        # - clock and reset information
        # - power interface outputs
        # - check condition
        
        cmds = []

        # 1. Set up the design
        design_files = self._get_design_files()
        for file in design_files:
            cmds.append('analyze -sv {}'.format(file))
        
        cmds += [
            'analyze -sv {}'.format(os.path.join(self._workdir, 'design_test.v')),
            'analyze -sv {}'.format(os.path.join(self._workdir, 'wrapper.v')),
            '',
            'elaborate -top wrapper',
            ''
        ]

        # 2. Source clock and reset information
        cmds += [
            'source {}'.format(self._clock_reset_info),
            ''
        ]

        # 3. Assumptions
        if ret_list is not None:
            for reg in self._regs:
                reg_renamed = rename_to_test_sig(reg)
                if reg in ret_list:
                    cmds += [ 'assume -env {{ {}_ret == 1\'b1 }}'.format(reg_renamed) ]
                else:
                    cmds += [ 'assume -env {{ {}_ret == 1\'b0 }}'.format(reg_renamed) ]
            cmds += ['']

        # 4. Assertions
        power_out_equivs = [ '({} == {}_test)'.format(out, out) for out in self._power_outputs ]
        non_power_out_equivs = [ '({} == {}_test)'.format(out, out) for out in self._non_power_outputs ]

        cmds += [
            'assert -disable {.*} -regexp',
            '',
            'assert -name output_equiv {{ @(posedge {}) disable iff ({})'.format(self._clock, self._reset),
            '    ( ' + ' &&\n    '.join(power_out_equivs) + ' ) &&',
            '    ( !({}) ||'.format(self._check_cond),
            '    ( ' + ' &&\n    '.join(non_power_out_equivs) + ' ) )',
            '}',
            ''
        ]

        # TODO: configuration
        cmds.append('set_engine_mode auto')
        # set_engine_mode -auto 8
        # set_proofgrid_per_engine_max_jobs 2

        cmds.append('set_prove_time_limit {}s'.format(Config.DEFAULT_TIMEOUT))

        cmds.append('')

        # 5. Prove the properties
        # TODO: prove -save_ppd?
        #ppd = os.path.join(self._workdir, 'ret_checker.ppd')

        cmds += [
            'prove -all -asserts',
            #'prove -property { output_equiv }',
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

        cmds.append('exit')

        return cmds
    
    
    def _get_design_info(self):
        """ Get design information (requires Jasper) """

        # Implemented in the Setup class
        # Results in error if the tool isn't set up properly
        self._logger.dump('Error: design_info.json does not exist in the config directory!!!')
        sys.exit(0)
    
    def _check_reg_subsets(self):
        """ Check if the retention, non-retention, and unknown register sets are set up properly """

        missing_regs = self._regs - self._ret_regs - self._non_ret_regs - self._unknown_regs
        if missing_regs:
            self._logger.dump('Error: The following registers are missing in the source file: {}'.format(missing_regs))
            sys.exit(0)
        
        def check_valid_subset(reg_subset):
            if not reg_subset.issubset(self._regs):
                self._logger.dump('Error: The following registers are invalid: {}'.format(reg_subset - self._regs))
                sys.exit(0)
        
        check_valid_subset(self._ret_regs)
        check_valid_subset(self._non_ret_regs)
        check_valid_subset(self._unknown_regs)

        def check_disjoint(reg_subset1, reg_subset2):
            if reg_subset1 & reg_subset2:
                self._logger.dump('Error: The following registers are in more than one subsets: {}'.format(reg_subset1 & reg_subset2))
                sys.exit(0)
        
        check_disjoint(self._ret_regs, self._non_ret_regs)
        check_disjoint(self._ret_regs, self._unknown_regs)
        check_disjoint(self._non_ret_regs, self._unknown_regs)
