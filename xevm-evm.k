require "xevm-evm-interface.k"
require "xevm-syntax.k"
require "evm-syntax.k"
require "lll-evm-config.k"

module XEVM-EVM
    imports XEVM-EVM-INTERFACE

    imports LLL-EVM-CONFIG

    imports XEVM-SYNTAX
    imports EVM-SYNTAX

    rule <k> xevm2evm => xevm2evm(Code) ... </k>
         <xevm> Code </xevm> // XEVM*

    syntax KItem ::= "xevm2evm" "(" List /* XEVM* */ ")"
    rule xevm2evm(Code) => genLabelTbl(Code) ~> decode(Code)

////

    rule genLabelTbl(.List) => .

    rule <k> genLabelTbl(ListItem(_:EVMCORE)       Code) => genLabelTbl(Code) ... </k> <pos> POS => POS +Int 1 </pos>
    rule <k> genLabelTbl(ListItem(DUP(_))          Code) => genLabelTbl(Code) ... </k> <pos> POS => POS +Int 1 </pos>
    rule <k> genLabelTbl(ListItem(SWAP(_))         Code) => genLabelTbl(Code) ... </k> <pos> POS => POS +Int 1 </pos>
    rule <k> genLabelTbl(ListItem(PUSH(N,_))       Code) => genLabelTbl(Code) ... </k> <pos> POS => POS +Int 1 +Int N </pos> // N bytes
    rule <k> genLabelTbl(ListItem(PUSH (label(_))) Code) => genLabelTbl(Code) ... </k> <pos> POS => POS        +Int 3 </pos> // PUSH2 highbits lowbits
    rule <k> genLabelTbl(ListItem(JUMP (label(_))) Code) => genLabelTbl(Code) ... </k> <pos> POS => POS +Int 1 +Int 3 </pos> // PUSH2 highbits lowbits
    rule <k> genLabelTbl(ListItem(JUMPI(label(_))) Code) => genLabelTbl(Code) ... </k> <pos> POS => POS +Int 1 +Int 3 </pos> // PUSH2 highbits lowbits
    rule <k> genLabelTbl(ListItem(JUMPI(pc))       Code) => genLabelTbl(Code) ... </k> <pos> POS => POS +Int 1 +Int 1 </pos> // PC

    rule <k> genLabelTbl(ListItem(CODELEN)         Code) => genLabelTbl(Code) ... </k> <pos> POS => POS        +Int 3 </pos> // PUSH2 highbits lowbits

    rule <k> genLabelTbl(ListItem(JUMPDEST(label(L))) Code) => genLabelTbl(Code) ... </k>
         <labelTbl> M => M[L <- POS] </labelTbl>
         <pos> POS => POS +Int 1 </pos>

    rule <k> genLabelTbl(ListItem(BLANK(label(L))) Code) => genLabelTbl(Code) ... </k>
         <labelTbl> M => M[L <- POS] </labelTbl>
         <pos> POS </pos>

    rule <k> genLabelTbl(ListItem(LLLBEGIN) Code) => genLabelTbl(Code) ... </k>
         <pos> POS => 0 </pos>
         <posStack> (.List => ListItem(POS)) ... </posStack>

    rule <k> genLabelTbl(ListItem(LLLEND) Code) => genLabelTbl(Code) ... </k>
         <pos> POS => POS +Int POS' </pos>
         <posStack> (ListItem(POS') => .List) ... </posStack>

////

    syntax KItem ::= "decode" "(" List /* XEVM* */ ")"

    rule decode(.List) => .

    rule <k> decode(ListItem(C:EVM) Code) => decode(Code) ... </k>
         <evm> ... (.List => ListItem(C)) </evm>

    rule     decode(ListItem(DUP(N))          Code) => decode(ListItem(decode1(DUP(N))))    ~>                   decode(Code)
    rule     decode(ListItem(SWAP(N))         Code) => decode(ListItem(decode1(SWAP(N))))   ~>                   decode(Code)
    rule     decode(ListItem(PUSH(N, B))      Code) => decode(ListItem(decode1(PUSH(N,B)))) ~> decodeBytes(B) ~> decode(Code)

    rule <k> decode(ListItem(CODELEN)         Code) => decodeInt(POS) ~>       decode(                   Code) ... </k> <pos> POS </pos>
    rule <k> decode(ListItem(PUSH (label(L))) Code) => decodeInt(M[L]:>Int) ~> decode(                   Code) ... </k> <labelTbl> M </labelTbl> when L in keys(M)
    rule <k> decode(ListItem(JUMP (label(L))) Code) => decodeInt(M[L]:>Int) ~> decode(ListItem(JUMP)     Code) ... </k> <labelTbl> M </labelTbl> when L in keys(M)
    rule <k> decode(ListItem(JUMPI(label(L))) Code) => decodeInt(M[L]:>Int) ~> decode(ListItem(JUMPI)    Code) ... </k> <labelTbl> M </labelTbl> when L in keys(M)
    rule     decode(ListItem(JUMPI(pc))       Code) =>            decode(ListItem(PC) ListItem(JUMPI)    Code)
    rule     decode(ListItem(JUMPDEST(_))     Code) =>                         decode(ListItem(JUMPDEST) Code)
    rule     decode(ListItem(BLANK(_))        Code) =>                         decode(                   Code)

    rule     decode(ListItem(LLLBEGIN)        Code) =>                         decode(                   Code)
    rule     decode(ListItem(LLLEND)          Code) =>                         decode(                   Code)

    syntax KItem ::= "decodeInt" "(" Int ")"
    rule <k> decodeInt(N) => . ... </k>
         <evm> ... (.List => ListItem(PUSH2) ListItem(N /Int 256) ListItem(N %Int 256)) </evm>
    when 0 <=Int N andBool N <Int (2 ^Int 16)

    syntax KItem ::= "decodeBytes" "(" Bytes ")"
    rule <k> decodeBytes(B Bs) => decodeBytes(Bs) ... </k>
         <evm> ... (.List => ListItem(B)) </evm>
    rule decodeBytes(.Bytes) => .

////

    syntax EVM ::= "decode1" "(" XEVM ")" [function]

    rule decode1(DUP(1 )) => DUP1
    rule decode1(DUP(2 )) => DUP2
    rule decode1(DUP(3 )) => DUP3
    rule decode1(DUP(4 )) => DUP4
    rule decode1(DUP(5 )) => DUP5
    rule decode1(DUP(6 )) => DUP6
    rule decode1(DUP(7 )) => DUP7
    rule decode1(DUP(8 )) => DUP8
    rule decode1(DUP(9 )) => DUP9
    rule decode1(DUP(10)) => DUP10
    rule decode1(DUP(11)) => DUP11
    rule decode1(DUP(12)) => DUP12
    rule decode1(DUP(13)) => DUP13
    rule decode1(DUP(14)) => DUP14
    rule decode1(DUP(15)) => DUP15
    rule decode1(DUP(16)) => DUP16

    rule decode1(SWAP(1 )) => SWAP1
    rule decode1(SWAP(2 )) => SWAP2
    rule decode1(SWAP(3 )) => SWAP3
    rule decode1(SWAP(4 )) => SWAP4
    rule decode1(SWAP(5 )) => SWAP5
    rule decode1(SWAP(6 )) => SWAP6
    rule decode1(SWAP(7 )) => SWAP7
    rule decode1(SWAP(8 )) => SWAP8
    rule decode1(SWAP(9 )) => SWAP9
    rule decode1(SWAP(10)) => SWAP10
    rule decode1(SWAP(11)) => SWAP11
    rule decode1(SWAP(12)) => SWAP12
    rule decode1(SWAP(13)) => SWAP13
    rule decode1(SWAP(14)) => SWAP14
    rule decode1(SWAP(15)) => SWAP15
    rule decode1(SWAP(16)) => SWAP16

    rule decode1(PUSH(1 , _)) => PUSH1
    rule decode1(PUSH(2 , _)) => PUSH2
    rule decode1(PUSH(3 , _)) => PUSH3
    rule decode1(PUSH(4 , _)) => PUSH4
    rule decode1(PUSH(5 , _)) => PUSH5
    rule decode1(PUSH(6 , _)) => PUSH6
    rule decode1(PUSH(7 , _)) => PUSH7
    rule decode1(PUSH(8 , _)) => PUSH8
    rule decode1(PUSH(9 , _)) => PUSH9
    rule decode1(PUSH(10, _)) => PUSH10
    rule decode1(PUSH(11, _)) => PUSH11
    rule decode1(PUSH(12, _)) => PUSH12
    rule decode1(PUSH(13, _)) => PUSH13
    rule decode1(PUSH(14, _)) => PUSH14
    rule decode1(PUSH(15, _)) => PUSH15
    rule decode1(PUSH(16, _)) => PUSH16
    rule decode1(PUSH(17, _)) => PUSH17
    rule decode1(PUSH(18, _)) => PUSH18
    rule decode1(PUSH(19, _)) => PUSH19
    rule decode1(PUSH(20, _)) => PUSH20
    rule decode1(PUSH(21, _)) => PUSH21
    rule decode1(PUSH(22, _)) => PUSH22
    rule decode1(PUSH(23, _)) => PUSH23
    rule decode1(PUSH(24, _)) => PUSH24
    rule decode1(PUSH(25, _)) => PUSH25
    rule decode1(PUSH(26, _)) => PUSH26
    rule decode1(PUSH(27, _)) => PUSH27
    rule decode1(PUSH(28, _)) => PUSH28
    rule decode1(PUSH(29, _)) => PUSH29
    rule decode1(PUSH(30, _)) => PUSH30
    rule decode1(PUSH(31, _)) => PUSH31
    rule decode1(PUSH(32, _)) => PUSH32

endmodule
