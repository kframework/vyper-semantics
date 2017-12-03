#!/usr/bin/env python3

import sys
import os
import subprocess
import re

from scripts.viper_parser import main as parse # string -> string
from scripts.op2byte import encode as op2byte # string list -> bytes

path = os.path.dirname(os.path.realpath(__file__))

def krun(kdir, pgm): # string * string -> string
    p = subprocess.run(['krun', '-d', os.path.join(path, kdir), '-cPGM=' + pgm, '-pPGM=kast -e'], stdout=subprocess.PIPE, stderr=subprocess.PIPE, encoding='utf-8')
    if p.returncode == 0:
        return p.stdout
    else:
        raise RuntimeError(p.stderr)

def viper2lll(ast): # string -> string
    out = krun('viper-lll', ast)
    lll = re.search(r'<lll> (.*) </lll>', out).group(1)
    return lll

def lll2evm(lll): # string -> string list
    out = krun('lll-evm', lll)
    evm = re.compile(r' \) ListItem \( ').sub(' ', re.search(r'<evm> ListItem \( (.*) \) </evm>', out).group(1))
    return evm.split(' ')

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("no input file")
        sys.exit(1)
    with open(sys.argv[1], "r") as fin:
        code = fin.read()
    ast = parse(code)
    lll = viper2lll(ast)
    evm = lll2evm(lll) # list of opcodes
    print('0x' + op2byte(evm).hex())
