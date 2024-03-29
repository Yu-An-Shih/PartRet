#!/usr/bin/env python3

# TODO: license

import time

class Timer():
    """ Record timing information """

    def __init__(self, logger):
        """ Initialize the timer """

        self._logger = logger
        
        self._start_time = time.time()

        self._iter = 0

        self._pf_rounds = 0
        self._pf_time_tot = 0

        self._cex_rounds = 0
        self._cex_time_tot = 0
    
    def get_elapsed_time(self) -> float:
        """ Get the elapsed time """

        return time.time() - self._start_time
    
    def start_iteration(self):
        """ Start a new iteration """

        self._iter += 1
        self._logger.dump('### Iteration {} ###'.format(self._iter))
    
    def get_iterations(self) -> int:
        """ Get number of iterations """
        
        return self._iter
    
    def update_time(self, res: dict):
        """ Update timing information """

        if res['result'] == 'proven':
            self._pf_rounds += 1
            self._pf_time_tot += res['time']
        elif res['result'] == 'cex':
            self._cex_rounds += 1
            self._cex_time_tot += res['time']
    
    #def get_pf_rounds(self) -> int:
    #    """ Get the number of rounds for proving """
    #
    #    return self._pf_rounds
    #
    #def get_cex_rounds(self) -> int:
    #    """ Get the number of rounds for finding counterexamples """
    #
    #    return self._cex_rounds
    
    def get_avg_pf_time(self) -> float:
        """ Get the average time for proving """

        return self._pf_time_tot / self._pf_rounds

    def get_avg_cex_time(self) -> float:
        """ Get the average time for finding counterexamples """

        return self._cex_time_tot / self._cex_rounds
    