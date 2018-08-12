#!/usr/bin/env python3.6

import py
from vyper import compiler

import os.path

# importing parent dir, where kvyper.py is located
# sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from kvyper_test import compile

old_gas_estimate = compiler.gas_estimate


def gas_estimate(origcode, *args, **kwargs):
    o = old_gas_estimate(origcode, args, kwargs)
    o2 = {}
    for key in o:
        o2[key] = 1000000000
    return o2


if __name__ == '__main__':
    # patching vyper.compiler.Compiler.compile
    compiler.compile = lambda code, *args, **kwargs: compile(code)

    # disabling gas estimation
    compiler.gas_estimate = lambda code, *args, **kwargs: gas_estimate(code, args, kwargs)

    # changing working directory to vyper repo. Required for tests that load other files.
    os.chdir("../vyper")

    py.test.cmdline.main()  # invoking pytest with args received from command line
