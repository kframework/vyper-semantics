import py
from viper import compiler

import sys
import os.path

# importing parent dir, where kviper.py is located
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from kviper import compile


def gas_estimate(origcode, *args, **kwargs):
    o = compiler.gas_estimate(origcode, args, kwargs)
    o2 = {}
    for key in o:
        o2[key] = 1000000000
    return o2


if __name__ == '__main__':
    # patching viper.compiler.Compiler.compile
    compiler.Compiler.compile = lambda self, code, *args, **kwargs: compile(code)
    compiler.compile = lambda code, *args, **kwargs: compile(code)

    # disabling gas estimation
    compiler.Compiler.gas_estimate = lambda self, code, *args, **kwargs: gas_estimate(code, args, kwargs)

    # changing working directory to viper repo. Required for tests that load other files.
    os.chdir("../viper")

    py.test.cmdline.main()  # invoking pytest with args received from command line
