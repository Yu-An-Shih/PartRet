#!/usr/bin/env python3

# ==============================================================================
# MIT License
# 
# Copyright (c) 2024 Yu-An-Shih
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
# ==============================================================================

import argparse
import json
import os
import time

from partret.checker.explorer import Explorer
from partret.util.logger import Logger
from partret.util.setup import Setup

def main():
    """ main function with command line interface """

    # command line argument parser
    parser = argparse.ArgumentParser(
        description='PartRet - Checking the correctness of partial retention for UPF files')
    
    # required arguments
    parser.add_argument('config', type=str, help='configuration file')

    # checker selection
    parser.add_argument('--setup', action='store_true',
                        help='set up files and scripts required for the partial retention check')
    #parser.add_argument('--explore', type=str, default='',
    #                    help='explore (minimize/complete) the retention register list')
    parser.add_argument('--optimize', type=str, default='combine',
                        help='optimize (set-explore/cex-guided/combine) the retention register list')

    # optional arguments
    #parser.add_argument('--src', type=str, default='',
    #                    help='source check point (to start)')
    #parser.add_argument('--dst', type=str, default='solution.json',
    #                    help='run-time check point (screenshot)')
    parser.add_argument('-o', '--out', type=str, default='checker.log',
                        help='log file')
    parser.add_argument('-w', '--work', type=str, default='work',
                        help='dir for temp files')
    parser.add_argument('-v', '--verbosity', type=int, default=0,
                        help='verbosity level')
    
    # TODO
    parser.add_argument('--opt', action='store_true',
                        help='run Yosys optimization pass on the partial retention circuit')

    args = parser.parse_args()

    # logger
    logger = Logger(args.out)

    # config
    if os.path.isfile(args.config):
        with open(args.config, 'r') as f:
            config = json.load(f)
    
    if not config or not isinstance(config, dict):
        logger.dump('Error: unable to load the config file: {}!!!'.format(args.config))
        return None

    # TODO: update config based on the command line arguments

    # update config with optional arguments
    #config['cpsrc'] = args.src
    #config['cpdst'] = args.dst

    #start_time = time.time()
    
    # set up
    if args.setup:
        Setup(config, logger, args.work, args.verbosity)
        return None
    
    #if args.explore:
    #    explorer = Explorer(config, logger, args.work, args.verbosity)
#
    #    if args.explore == 'minimize':
    #        explorer.minimize_retention_list()
    #    elif args.explore == 'complete':
    #        explorer.complete_retention_list()
    #    else:
    #        logger.dump('Error: unknown exploration method {}'.format(args.explore))
    
    if args.optimize:
        explorer = Explorer(config, logger, args.work, args.verbosity)

        if args.optimize == 'combine':
            explorer.optimize_retention_list()
        elif args.optimize == 'set-explore':
            explorer.retention_set_exploration()
        elif args.optimize == 'cex-guided':
            explorer.cex_guided_retention_search()
        else:
            logger.dump('Error: unknown optimization method {}'.format(args.optimize))
    
    #end_time = time.time()
    #logger.dump('Execution time: {:.2f} seconds'.format(end_time - start_time))


if __name__ == '__main__':
    main()
