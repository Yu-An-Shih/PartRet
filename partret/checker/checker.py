#!/usr/bin/env python3

# TODO: license

import json
import os
import sys
import tempfile

from partret.config import Config
from partret.solver.jasper import JasperSolver
from partret.solver.yosys import YosysSolver
#from partret.util.image import Image


class Checker:
    """ Partial retention checker """

    def __init__(self, config, logger, workdir, verbosity=0):
        """ constructor """

        self._tmpdir = os.path.join(workdir, 'tmp') # stores temporary files for debug purpose
        if not os.path.exists(self._tmpdir):
            os.makedirs(self._tmpdir)
        
        self._logger = logger
        self._workdir = workdir
        self._verbosity = verbosity

        self._design_files = []

        self._clock = ""
        self._secondary_clocks = {}
        #self._reset = ""    # TODO: remove this
        self._resets = {}
        self._top_module = ""
        self._reset_input_vals = {}

        self._check_cond = ""

        # TODO: restore condition

        self._input_width_list = {}
        self._output_width_list = {}
        
        self._power_outputs = []
        self._non_power_outputs = []

        self._regs_and_resets = {}

        self._regs = set()
        self._ret_regs = set()
        self._non_ret_regs = set()
        self._unknown_regs = set()

        self._non_resettable_regs = []
        
        self._solver = JasperSolver(logger, workdir)
        self._ys_solver = YosysSolver(logger, workdir)
        
        self._setup(config)

        
    def _setup(self, config: dict):
        """ Set up checker based on the config file """

        # design files
        assert isinstance(config['RTL'], list)
        self._get_design_files(config['RTL'])

        # clock
        assert isinstance(config['clock'], str)
        self._clock = config['clock']

        if 'secondary_clocks' in config:
            assert isinstance(config['secondary_clocks'], dict)
            self._secondary_clocks = config['secondary_clocks']

        # reset
        #assert isinstance(config['reset'], str)
        #self._reset = config['reset']

        assert isinstance(config['resets'], dict)
        self._resets = config['resets']

        # top module
        assert isinstance(config['top_module'], str)
        self._top_module = config['top_module']

        #if 'top_module' in config:
        #    assert isinstance(config['top_module'], str)
        #    self._top_module = config['top_module']
        #else:
        #    self._logger.dump('Warning: top_module is not specified in the config file.')

        # input values during reset
        if 'reset_input_values' in config:
            assert isinstance(config['reset_input_values'], dict)
            self._reset_input_vals = config['reset_input_values']
        
        # check condition
        assert isinstance(config['check_condition'], str)
        self._check_cond = config['check_condition']

        # design information
        design_info = os.path.join(self._workdir, 'design_info.json')
        if not os.path.isfile(design_info):
            self._get_design_info()
        with open(design_info, 'r') as f:
            design_info = json.load(f)
        
        # input and output lists
        #excluded = [self._clock, self._reset] + list(self._secondary_clocks.keys())
        excluded = [self._clock] + list(self._secondary_clocks.keys()) + list(self._resets.keys())
        self._input_width_list = {input: width for input, width in design_info['input_list'].items() if input not in excluded}
        self._output_width_list = design_info['output_list']

        # power interface outputs
        assert isinstance(config['power_interface_outputs'], list)
        self._power_outputs = config['power_interface_outputs']
        self._non_power_outputs = list(set(design_info['output_list'].keys()) - set(self._power_outputs))

        # self._regs, self._ret_regs, self._non_ret_regs
        self._regs_and_resets = design_info['reset_values']
        self._regs = set(self._regs_and_resets.keys())

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

        # non-resettable registers
        if 'non_resettable_regs' in config:
            self._non_resettable_regs = config['non_resettable_regs']

    
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

    
    def _gen_partret_design(self, non_ret_list):
        ### Generate a partial retention design (requires Yosys) ###

        # Require
        # - RTL files
        # - top module

        # Temporary files
        # - get reset values list for non-retention registers
        reset_values_part = os.path.join(self._workdir, 'reset_values_part.txt')

        # Target content
        # - design_test.v: power-collapsible design
        design_test = os.path.join(self._workdir, 'design_test.v')

        # 1. Create a reset value list for non-retention registers
        with open(reset_values_part, 'w') as fw:
            for reg in non_ret_list:
                fw.write('{}\n{}\n'.format(reg, self._regs_and_resets[reg]))

        # 2. Call the Yosys passes to generate the partial retention circuit
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

            'rename -top {}_test'.format(self._top_module),

            #'make_power_collapsible -reset_vals {}'.format(reset_values),
            'gen_part_ret -reset_vals {}'.format(reset_values_part),

            'write_verilog -nodec -noattr -noparallelcase {}'.format(design_test)
        ]

        if self._verbosity > 0:
            # dump Yosys script
            with open(os.path.join(self._tmpdir, 'gen_design_test.ys'), 'w') as fw:
                print('\n'.join(cmds), file=fw)
        
        # lauch Yosys
        self._ys_solver._exec_yosys(cmds)

        os.remove(reset_values_part)

        # 3. Format the generated design_test.v
        # TODO: replace ' [*];' with '[*];'?
        #temp_fd, temp_path = tempfile.mkstemp(dir=self._workdir)
        #with os.fdopen(temp_fd, 'w') as temp_file, open(design_test, 'r') as infile:
        #    for line in infile:
        #        modified_line = line.replace('\\', '').replace(' ;', ';')
        #        temp_file.write(modified_line)
        #os.replace(temp_path, design_test)    
    
    
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
