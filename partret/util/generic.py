#!/usr/bin/env python3

# TODO: license


def rename_to_test_sig(golden_sig: str) -> str:
    return golden_sig.replace('.', '__').replace('[', '__').replace(']', '')