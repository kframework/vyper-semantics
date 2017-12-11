from viper.parser.parser import LLLnode

lll_opcodes = ['if', 'repeat', 'break', 'with', 'set', 'seq', 'pass', 'assert',
               'ne', 'le', 'ge', 'sle', 'sge', 'uclamplt', 'uclample', 'uclampgt',
               'uclampge', 'clamplt', 'clample', 'clampgt', 'clampge', 'uclamp', 'clamp',
               'clamp_nonzero', 'ceil32', 'sha3_32', '~codelen', 'codeload', 'lll',
               '_stloc', '_mloc', '_loc', 'l', 'r', 'ans', '_L', '_R', '_source', '_sz',
               '_pos', '_opos', '_actual_len', '_poz', '_s', '_sub', '_len', '_el1',
               '_start', '_length', '_l', '_r',
               # EVM Opcodes
               'stop', 'add', 'mul', 'sub', 'div', 'sdiv', 'mod', 'smod', 'addmod', 'mulmod',
               'exp', 'signextend', 'lt', 'gt', 'slt', 'sgt', 'eq', 'iszero', 'and', 'or',
               'xor', 'not', 'byte', 'sha3', 'address', 'balance', 'origin', 'caller', 'callvalue',
               'calldataload', 'calldatasize', 'calldatacopy', 'codesize', 'codecopy', 'gasprice',
               'extcodesize', 'extcodecopy', 'blockhash', 'coinbase', 'timestamp', 'number', 'difficulty',
               'gaslimit', 'pop', 'mload', 'mstore', 'mstore8', 'sload', 'sstore', 'msize', 'gas',
               'log0', 'log1', 'log2', 'log3', 'log4', 'create', 'call', 'callcode', 'return',
               'delegatecall', 'callblackbox', 'invalid', 'suicide', 'selfdestruct'
              ]

def print_lll_abstract(code):
    code_value = str(code.value)

    if code_value in lll_opcodes:
        if code_value == 'seq':
            code_value = '$%seq'
        elif code_value == '~codelen':
            code_value = '$codelen'
        else:
            code_value = '${}'.format(code_value)

    if not len(code.args):
        return code_value

    o = code_value + ' ( '
    sub_exprs = [print_lll_abstract(arg) for arg in code.args]
    subs = ' , '.join(sub_exprs)
    o+= subs
    o += ' )'

    return o
