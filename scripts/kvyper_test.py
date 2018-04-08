#!/usr/bin/env python3.6

import sys
import os
import subprocess
import re

from vyper_parser import main as parse  # string -> string
from vyper_parser import KVStructureException
from vyper_parser import KVTypeMismatchException
from op2byte import encode as op2byte  # string list -> bytes
from vyper import exceptions

path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))


def krun(kdir, pgm):  # string * string -> string
    try:
        p = subprocess.run(['krun', '-d', os.path.join(path, kdir), '-cPGM=' + pgm, '-pPGM=kast -e', '--debug'],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, encoding='utf-8')
    except FileNotFoundError as e:
        print("Error: subprocess.run() ended with FileNotFoundError for file: " + str(e.filename), file=sys.stderr)
        raise e

    if p.returncode == 0:
        return p.stdout
    else:
        raise RuntimeError(p.stderr)


def vyper2lll(ast):  # string -> string
    out = krun('vyper-lll', ast)
    print("\n{}\n\n".format(out))
    lll = re.search(r'<lll> (.*) </lll>', out).group(1)
    if lll == ".":
        exceptionRegex = re.search(r'<k> #exception \( "([^"]+)" \)', out)
        if exceptionRegex is not None:
            try_decode_exception(exceptionRegex.group(1))
            raise RuntimeError("vyper-lll exception:\n\n{}\n\n".format(out))
        raise RuntimeError("vyper-lll computation got stuck:\n\n" + out + "\n\n")

    return lll


def try_decode_exception(exceptionMsg):
    if "Persistent variable undeclared" in exceptionMsg \
            or "not declared" in exceptionMsg \
            or "Undeclared" in exceptionMsg \
            or "Variable name" in exceptionMsg \
            or "variable name" in exceptionMsg \
            or "Cannot declare" in exceptionMsg \
            or "not declared yet" in exceptionMsg \
            or "Duplicate" in exceptionMsg \
            or "Variable name duplicated" in exceptionMsg \
            or "Maximum of 3 topics" in exceptionMsg:
        raise exceptions.VariableDeclarationException(exceptionMsg)
    elif "Persistent variable undeclared" in exceptionMsg \
            or "Concat expects at least two arguments" in exceptionMsg \
            or "requires argument" in exceptionMsg \
            or "Unexpected argument" in exceptionMsg \
            or "Unsupported operator" in exceptionMsg \
            or "List must have elements" in exceptionMsg \
            or "Tuple must have elements" in exceptionMsg \
            or "Invalid contract reference" in exceptionMsg \
            or "Function visibility must be declared" in exceptionMsg \
            or "For loops allowed" in exceptionMsg \
            or "Tuple lengths don't match" in exceptionMsg:
        raise exceptions.StructureException(exceptionMsg)
    elif "constant function" in exceptionMsg \
            or "Cannot modify function argument" in exceptionMsg:
        raise exceptions.ConstancyViolationException(exceptionMsg)
    elif "in a non-payable function" in exceptionMsg:
        raise exceptions.NonPayableViolationException(exceptionMsg)
    elif "Cannot insert special character" in exceptionMsg \
            or "Number out of range" in exceptionMsg \
            or "Too many decimal places" in exceptionMsg \
            or "Cannot read 0x value" in exceptionMsg \
            or "Can only log" in exceptionMsg \
            or "Invalid input for uint256" in exceptionMsg \
            or "Invalid denomination" in exceptionMsg:
        raise exceptions.InvalidLiteralException(exceptionMsg)
    elif "Argument must have type" in exceptionMsg \
            or "type invalid" in exceptionMsg \
            or "base type" in exceptionMsg \
            or "Malformed unit type" in exceptionMsg \
            or "No mappings allowed" in exceptionMsg \
            or "Mapping keys must be" in exceptionMsg \
            or "Invalid member variable for struct" in exceptionMsg \
            or "Invalid type" in exceptionMsg \
            or "Byte array length must be a number" in exceptionMsg \
            or "Bad byte array length" in exceptionMsg \
            or "Invalid base unit" in exceptionMsg \
            or "Invalid unit expression" in exceptionMsg \
            or "Invalid units" in exceptionMsg \
            or "Can only raise a base type to an exponent" in exceptionMsg \
            or "Exponent must be positive integer" in exceptionMsg \
            or "Mismatched number of elements" in exceptionMsg \
            or "Typecasting" in exceptionMsg \
            or "Unsupported type" in exceptionMsg \
            or "Units must be compatible" in exceptionMsg \
            or "Boolean operations can only be between booleans" in exceptionMsg \
            or "Cannot cast" in exceptionMsg \
            or "mismatch" in exceptionMsg \
            or "Trying to return" in exceptionMsg \
            or "Only whole number exponents" in exceptionMsg \
            or "to return a value" in exceptionMsg \
            or "Return list length" in exceptionMsg \
            or "Keys don't match" in exceptionMsg \
            or "Cannot copy mappings" in exceptionMsg \
            or "Member variable duplicated" in exceptionMsg \
            or "does not match" in exceptionMsg \
            or "Minmax types incompatible" in exceptionMsg \
            or "don't match" in exceptionMsg \
            or "Expecting one of" in exceptionMsg \
            or "Can't compare values" in exceptionMsg \
            or "keyword expects" in exceptionMsg \
            or "Type for" in exceptionMsg \
            or "positional" in exceptionMsg:
        raise exceptions.TypeMismatchException(exceptionMsg)
    elif "Invalid unit" in exceptionMsg:
        raise exceptions.InvalidTypeException(exceptionMsg)


def lll2evm(lll):  # string -> string list
    out = krun('lll-evm', lll)
    # print("\n{}\n\n".format(out))

    if "<k> . </k>" in out:
        evm = re.compile(r' \) ListItem \( ').sub(' ', re.search(r'<evm> ListItem \( (.*) \) </evm>', out).group(1))
        return evm.split(' ')
    else:
        raise RuntimeError("lll-evm computation got stuck:\n\n" + out + "\n\n")


def compile(code):  # string -> bytes
    print("\n{}\n\n".format(code))

    try:
        ast = parse(code)
    except KVStructureException as e:
        raise exceptions.StructureException(str(e))
    except KVTypeMismatchException as e:
        raise exceptions.TypeMismatchException(str(e))

    print("\n{}\n\n".format(ast))

    lll = vyper2lll(ast)
    evm = lll2evm(lll)  # list of opcodes
    return op2byte(evm)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("no input file")
        sys.exit(1)
    with open(sys.argv[1], "r") as fin:
        code = fin.read()
    print('0x' + compile(code).hex())
