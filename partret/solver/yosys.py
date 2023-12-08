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
                res = subprocess.run(['yosys', '-m', 'partret/util/yosys/make_power_collapsible.so', cmd_file.name], stdout=subprocess.PIPE)
            except BaseException:
                self._logger.dump('Error during solving:')
                self._logger.dump('\n'.join(cmds))
                sys.exit(0)

        return res.stdout.decode('utf-8')