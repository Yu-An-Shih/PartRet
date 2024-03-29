#!/usr/bin/env python3

# TODO: license

import os
import subprocess
import sys
import tempfile

class SimulatorSolver:
    """ Solver interface for a simulator """

    def __init__(self, config, design_files, logger, workdir):
        """ Constructor """

        self._logger = logger
        self._workdir = workdir

        wrapper = os.path.join(self._workdir, 'wrapper_sim.sv')
        design_test = os.path.join(self._workdir, 'design_test.v')
        self._tb_files = design_files + [wrapper, design_test]
        self._compiled_file = os.path.join(self._workdir, 'tb')

        self._include_dirs = []
        self._get_include_dirs(config['RTL'])

    
    def exec(self):
        """ Compile and simulate the testbench"""
        pass
    
    
    def _get_include_dirs(self, rtl=[]):
        """ Get the list of directories searched for Verilog include files """
        
        if not self._include_dirs:
            for path in rtl:
                if os.path.isdir(path):
                    self._include_dirs.append(path)
        
        return self._include_dirs
    
    @staticmethod
    def is_cex(msg: str) -> bool:
        pass


class IcarusSolver(SimulatorSolver):
    """ Solver interface for the Icarus Verilog simulator """

    def __init__(self, config, design_files, logger, workdir):
        """ Constructor """

        super().__init__(config, design_files, logger, workdir)
    
    def exec(self):
        """ Compile and simulate the testbench"""

        compile_cmd = ['iverilog', '-o', self._compiled_file] + self._tb_files
        for dir in self._include_dirs:
            compile_cmd += ['-I', dir]
        
        simulate_cmd = ['vvp', self._compiled_file]

        try:
            subprocess.run(compile_cmd, stdout=subprocess.PIPE)
            res = subprocess.run(simulate_cmd, stdout=subprocess.PIPE)
        except BaseException:
            self._logger.dump('Error during solving:')
            self._logger.dump('\n'.join([' '.join(compile_cmd), ' '.join(simulate_cmd)]))
            sys.exit(0)
        
        os.remove(self._compiled_file)
        
        return res.stdout.decode('utf-8')
    
    @staticmethod
    def is_cex(msg: str) -> bool:
        
        res = msg.strip().split('\n')[-1]

        if res == 'cex':
            return True
        else:
            assert res == 'proven'
            return False


class VCSSolver(SimulatorSolver):
    """ Solver interface for the Synopsys VCS simulator """

    def __init__(self, config, design_files, logger, workdir):
        """ Constructor """

        super().__init__(config, design_files, logger, workdir)
    
    def exec(self):
        """ Compile and simulate the testbench"""

        #vcs_alias = '/usr/licensed/bin/run7 /usr/licensed/synopsys/vcs-mx/O-2018.09-SP2/bin/vcs'
        compile_cmd = ['/usr/licensed/bin/run7', '/usr/licensed/synopsys/vcs-mx/O-2018.09-SP2/bin/vcs', '-full64 -sverilog +v2k +notimingcheck', '-Mdir={}'.format(os.path.join(self._workdir, 'csrc')), '-o', self._compiled_file] + self._tb_files
        
        if self._include_dirs:
            compile_cmd += ['+incdir+' + '+'.join(self._include_dirs)]
        
        simulate_cmd = [self._compiled_file]

        try:
            subprocess.run(compile_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            res = subprocess.run(simulate_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        except BaseException:
            self._logger.dump('Error during solving:')
            self._logger.dump('\n'.join([' '.join(compile_cmd), ' '.join(simulate_cmd)]))
            sys.exit(0)
        
        os.remove(self._compiled_file)
        os.remove('ucli.key')
        
        return res.stdout.decode('utf-8')
    
    @staticmethod
    def is_cex(msg: str) -> bool:

        res = msg.split('$finish')[0].strip().split('\n')[-1]
        
        if res == 'cex':
            return True
        else:
            assert res == 'proven'
            return False
