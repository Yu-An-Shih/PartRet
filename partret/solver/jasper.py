#!/usr/bin/env python3

# TODO: license

import os
import subprocess
import sys
import tempfile


class JasperSolver:
    """ Solver interface for Jasper """

    def __init__(self, logger, workdir):
        """ Constructor """

        self._logger = logger
        assert os.path.isdir(workdir)
        self._workdir = workdir
    
    def _exec_jg(self, cmds : list):
        """ Launch Jasper with the commands """
        
        with tempfile.NamedTemporaryFile(suffix='.tcl', dir=self._workdir) as cmd_file:

            with open(cmd_file.name, 'w') as fw:
                print('\n'.join(cmds), file=fw)

            with tempfile.TemporaryDirectory(dir=self._workdir) as proj_dir:
                try:
                    res = subprocess.run(['jg', '-no_gui', '-tcl', cmd_file.name, '-proj', proj_dir], stdout=subprocess.PIPE)
                except BaseException:
                    self._logger.dump('Error during solving:')
                    self._logger.dump('\n'.join(cmds))
                    sys.exit(0)

        return res.stdout.decode('utf-8')

    
    def _parse_jg_result(self, out_msg):
        """ Parse Jasper output """
        
        # get the proof result (proved/cex/max_trace_length)
        try:
            summary = out_msg.split('SUMMARY')[1]
            #summary = out_msg.split('INFO (IPF059): ')[1]   # INFO (IPF059): Completed proof on task ...
        except BaseException:
            self._logger.dump('Fail getting proof sumamry')
            return out_msg
        
        # helper - extract solving info
        def extract_info(key, assert_name):
            ##############################
            # Example:
            #   [<embedded>] % get_property_info "output_equiv_pow" -list status
            #   cex
            #   [<embedded>] % ...
            ##############################
            prefix = 'get_property_info {} -list {}\n'.format(assert_name, key)
            suffix = '\n[<embedded>]'

            info_str = summary.split(prefix)[1]
            info_str = info_str.split(suffix)[0]
            info_str = info_str.strip()

            return info_str
        
        all_res = {}

        for ass in ['output_equiv']:
            res = {}

            # solving status (cex/proven/undetermined)
            status = extract_info('status', ass)
            assert status == 'cex' or status == 'proven' or status == 'undetermined'

            res['result'] = status

            # time
            time_str = extract_info('time', ass)
            res['time'] = float(time_str)

            # depth
            # TODO: What do these numbers mean?
            if status == 'proven':
                depth_str = extract_info('proof_effort', ass)
            elif status == 'undetermined':
                depth_str = extract_info('min_length', ass)
            else:
                depth_str = extract_info('trace_length', ass)
            
            res['depth'] = int(depth_str)

            # engine
            engine = extract_info('engine', ass)
            res['engine'] = engine

            # update
            all_res[ass] = res
        
        return all_res

    @staticmethod
    def is_proven(results: dict) -> bool:
        # e.g. results = {'output_equiv_pow': {'result': 'cex'}, 'output_equiv': {'result': 'cex'}}
        
        for res in results.values():
            if res['result'] != 'proven':
                return False
        
        return True