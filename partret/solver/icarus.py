#!/usr/bin/env python3

# TODO: license

import os
import subprocess
import sys
import tempfile

class IcarusSolver:
    """ Solver interface for the Icarus Verilog simulator """

    def __init__(self, config, logger, workdir):
        """ Constructor """

        self._logger = logger
        self._workdir = workdir

        self._wrapper = os.path.join(self._workdir, 'wrapper_sim.sv')
        self._design_test = os.path.join(self._workdir, 'design_test.v')

        self._include_dirs = []
        self._get_include_dirs(config['RTL'])

    
    def exec(self, design_files: list):
        """ Compile and simulate the testbench"""

        tb_files = design_files + [self._wrapper, self._design_test]

        compiled_file = os.path.join(self._workdir, 'tb')

        compile_cmd = ['iverilog', '-o', compiled_file] + tb_files
        for dir in self._include_dirs:
            compile_cmd += ['-I', dir]
        
        simulate_cmd = ['vvp', compiled_file]

        try:
            subprocess.run(compile_cmd, stdout=subprocess.PIPE)
            res = subprocess.run(simulate_cmd, stdout=subprocess.PIPE)
        except BaseException:
            self._logger.dump('Error during solving:')
            self._logger.dump('\n'.join([' '.join(compile_cmd), ' '.join(simulate_cmd)]))
            sys.exit(0)
        
        os.remove(compiled_file)
        
        return res.stdout.decode('utf-8')
    
    
    def _get_include_dirs(self, rtl=[]):
        """ Get the list of directories searched for Verilog include files """
        
        if not self._include_dirs:
            for path in rtl:
                if os.path.isdir(path):
                    self._include_dirs.append(path)
        
        return self._include_dirs
    
    @staticmethod
    def is_cex(msg: str) -> bool:
        
        res = msg.strip().split('\n')[-1]

        if res == 'cex':
            return True
        else:
            assert res == 'proven'
            return False
    
