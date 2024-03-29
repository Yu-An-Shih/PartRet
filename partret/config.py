#!/usr/bin/env python3

# TODO: license

class Config:
    """ Arch configurations """

    # Analyze the clock with both edges
    # - JasperGold
    #   - clock clk -both_edges
    #CLOCK_BOTH_EDGES = False

    # The #cycles before the INIT step.
    # - For encoder:
    #   - ASSERT: steps before this number is not asserted
    #   - ASSUME: ASSUME_INIT & ASSUME_EXEC will be shifted with this number
    # - For solver:
    #   - solver bound = user bound + bias
    #COUNTER_BIAS = 0

    # Default timeout for each query
    # - JasperGold
    #   - set_prove_time_limit {}s
    DEFAULT_VERIF_TIMEOUT = 86400

    # Default timeout for the algorithm (seconds)
    DEFAULT_TIMEOUT = 86400
