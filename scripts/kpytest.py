import py
from viper import compiler

import sys
import os.path
# importing parent dir, where kviper.py is located
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from kviper import compile

if __name__ == '__main__':
    # patching viper.compiler.Compiler.compile
    compiler.Compiler.compile = lambda self, code, *args, **kwargs: compile(code)
    py.test.cmdline.main() # invoking pytest with args received from command line

# todo - patch regular compile method too, it's directly invoked from many tests
