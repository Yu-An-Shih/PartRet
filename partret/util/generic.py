#!/usr/bin/env python3

# TODO: license


def rename_to_test_sig(golden_sig: str) -> str:
    #return golden_sig.replace('.', '__').replace('[', '__').replace(']', '')
    if '.' in golden_sig:
        test_sig = '\\' + golden_sig.replace('[', ' [')
    else:
        test_sig = golden_sig
    
    return test_sig