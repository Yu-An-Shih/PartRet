#!/usr/bin/env python3

# TODO: license

#import os
import subprocess
import sys
import tempfile

class YosysSolver:
    """ Solver interface for Jasper """

    def __init__(self, logger, workdir):
        """ Constructor """

        self._logger = logger
        self._workdir = workdir
    
    def _exec_yosys(self, cmds : list):
        """ Launch Yosys with the commands """
        
        with tempfile.NamedTemporaryFile(suffix='.ys', dir=self._workdir) as cmd_file:

            with open(cmd_file.name, 'w') as fw:
                print('\n'.join(cmds), file=fw)
            
            try:
                res = subprocess.run(['yosys', '-m', 'partret/util/yosys/gen_part_ret.so', cmd_file.name], check=True, text=True, capture_output=True)
            except subprocess.CalledProcessError as e:
                self._logger.dump('Command "{}" failed:'.format(' '.join(e.cmd)))
                self._logger.dump(e.stderr)
                sys.exit(0)

        return res.stdout
    
    @staticmethod
    def rename_to_test_sig(golden_sig: str) -> str:
        
        #return golden_sig.replace('.', '__').replace('[', '__').replace(']', '')
        
        if '.' in golden_sig:
            test_sig = '\\' + golden_sig.replace('[', ' [')
        else:
            test_sig = golden_sig
        
        return test_sig