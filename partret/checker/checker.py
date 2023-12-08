#!/usr/bin/env python3

# TODO: license

import json
import os
import sys

from partret.config import Config
from partret.solver.jasper import JasperSolver
from partret.util.generic import rename_to_test_sig
from partret.util.image import Image


class Checker:
    """ TODO """

    def __init__(self, config_dir, logger, workdir, verbosity=0):
        """ constructor """
        
        self._config_dir = config_dir
        self._logger = logger
        self._workdir = workdir
        self._verbosity = verbosity

        self._design_files = []

        self._clock = ""
        self._reset = ""

        self._power_outputs = []
        self._non_power_outputs = []

        self._regs = set()
        self._ret_regs = set()
        self._non_ret_regs = set()
        self._unknown_regs = set()

        self._solver = JasperSolver(logger, workdir)

        config_file = os.path.join(config_dir, 'config.json')
        assert os.path.isfile(config_file)
        with open(config_file, 'r') as f:
            config = json.load(f)
        
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
        if 'top_module' in config:
            assert isinstance(config['top_module'], str)
            self._top_module = config['top_module']
        else:
            self._logger.dump('Warning: top_module is not specified in the config file.')
        
        # clock and reset information (for Jasper)
        self._clock_reset_info = config['clock_reset_info']
        assert os.path.isfile(self._clock_reset_info)
        
        # standby condition
        assert isinstance(config['standby_condition'], str)
        self._standby_cond = config['standby_condition']

        # check condition
        assert isinstance(config['check_condition'], str)
        self._check_cond = config['check_condition']

        # design information
        design_info = os.path.join(self._config_dir, 'design_info.json')
        if not os.path.isfile(design_info):
            self._get_design_info()
        with open(design_info, 'r') as f:
            design_info = json.load(f)
        
        # output lists
        assert isinstance(config['power_interface_outputs'], list)
        self._power_outputs = config['power_interface_outputs']
        self._non_power_outputs = list(set(design_info['output_list'].keys()) - set(self._power_outputs))

        # self._regs, self._ret_regs, self._non_ret_regs
        self._regs = set(design_info['register_list'].keys())

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

        # destination
        assert isinstance(config['dst'], str)
        self._dst = Image(self._logger, config['dst'])

    
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

    
    def _gen_ret_checker(self, ret_list):
        """ Generate a proof script (ret_checker.tcl) for the target retention list """

        cmds = []

        # 1. Set up the design
        design_files = self._get_design_files()
        for file in design_files:
            cmds.append('analyze -sv {}'.format(file))
        
        cmds += [
            'analyze -sv {}'.format(os.path.join(self._config_dir, 'design_test.v')),
            'analyze -sv {}'.format(os.path.join(self._config_dir, 'wrapper.v')),
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
