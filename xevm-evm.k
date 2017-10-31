require "xevm-syntax.k"
require "evm-syntax.k"

module XEVM-EVM-SYNTAX
    syntax KItem ::= "xevm2evm"
endmodule

module XEVM-EVM
    imports XEVM-SYNTAX
    imports EVM-SYNTAX
    imports XEVM-EVM-SYNTAX

    rule <k> xevm2evm => xevm2evm(Code) ... </k>
         <xevm> Code /* XEVM* */ </xevm>

    syntax KItem ::= "xevm2evm" "(" List /* XEVM* */ ")"
    rule xevm2evm(Code) => genSymTbl(Code) ~> decode(Code)

////

    rule genSymTbl(.List) => .

    rule <k> genSymTbl(ListItem(_:EVMCORE) Code) => genSymTbl(Code) ... </k> <pos> POS => POS +Int 1 </pos>
    rule <k> genSymTbl(ListItem(DUP(_))    Code) => genSymTbl(Code) ... </k> <pos> POS => POS +Int 1 </pos>
    rule <k> genSymTbl(ListItem(SWAP(_))   Code) => genSymTbl(Code) ... </k> <pos> POS => POS +Int 1 </pos>
    rule <k> genSymTbl(ListItem(PUSH(N,_)) Code) => genSymTbl(Code) ... </k> <pos> POS => POS +Int 1 +Int N </pos>
    rule <k> genSymTbl(ListItem(PUSH(_))   Code) => genSymTbl(Code) ... </k> <pos> POS => POS +Int 1 +Int 2 </pos> // label: 2 bytes
    rule <k> genSymTbl(ListItem(JUMP(_))   Code) => genSymTbl(Code) ... </k> <pos> POS => POS +Int 1 +Int 3 </pos> // push(label)
    rule <k> genSymTbl(ListItem(JUMPI(_))  Code) => genSymTbl(Code) ... </k> <pos> POS => POS +Int 1 +Int 3 </pos> // push(label)

    rule <k> genSymTbl(ListItem(CODELEN)   Code) => genSymTbl(Code) ... </k> <pos> POS => POS +Int 3 </pos> // push(label)

    rule <k> genSymTbl(ListItem(JUMPDEST(L)) Code) => genSymTbl(Code) ... </k>
         <labelTbl> M => M[L <- POS] </labelTbl>
         <pos> POS </pos>

////

    syntax KItem ::= "decode" "(" List /* XEVM* */ ")"

    rule <k> decode(ListItem(C:EVMCORE)   Code) => decode(Code) ... </k> <evm> ... (.List => ListItem(C)) </evm>

    rule <k> decode(ListItem(DUP(N))      Code) => decode(Code) ... </k> <evm> ... (.List => decode1(DUP(N))) </evm>
    rule <k> decode(ListItem(SWAP(N))     Code) => decode(Code) ... </k> <evm> ... (.List => decode1(SWAP(N))) </evm>
    rule <k> decode(ListItem(PUSH(N, B))  Code) => decode(Code) ... </k> <evm> ... (.List => decode1(PUSH(N,B)) decodeBytes(B)) </evm>

    rule <k> decode(ListItem(PUSH(L))     Code) => decode(Code) ... </k> <evm> ... (.List => decodeInt(M[L]))                 </evm> <labelTbl> M </labelTbl>
    rule <k> decode(ListItem(JUMP(L))     Code) => decode(Code) ... </k> <evm> ... (.List => decodeInt(M[L]) ListItem(JUMP))  </evm> <labelTbl> M </labelTbl>
    rule <k> decode(ListItem(JUMPI(L))    Code) => decode(Code) ... </k> <evm> ... (.List => decodeInt(M[L]) ListItem(JUMPI)) </evm> <labelTbl> M </labelTbl>
    rule     decode(ListItem(JUMPDEST(_)) Code) => decode(Code)
    rule <k> decode(ListItem(CODELEN)     Code) => decode(Code) ... </k> <evm> ... (.List => decodeInt(POS)  ListItem(JUMPI)) </evm> <pos> POS </pos>

////

    syntax List ::= "decodeInt" "(" Int ")" [function]
    rule decodeInt(N) => ListItem(PUSH2) ListItem(N /Int 256) ListItem(N %Int 256)
    when 0 <=Int N andBool N <Int (2 ^Int 16)

    syntax List ::= "decodeBytes" "(" Bytes ")" [function]
    rule decodeBytes(B Bs) => ListItem(B) decodeBytes(Bs)
    rule decodeBytes(.Bytes) => .List

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
