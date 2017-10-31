require "lll-syntax.k"
require "xevm-syntax.k"
require "evm-syntax.k"
//require "xevm-evm.k"

module LLL-XEVM-SYNTAX
    imports LLL-SYNTAX
endmodule

module LLL-XEVM
    imports LLL-XEVM-SYNTAX
    imports XEVM-SYNTAX
    imports EVM-SYNTAX
//  imports XEVM-EVM

    configuration <T>
      <k> $PGM:LLLExp ~> xevm2evm </k>
      <xevm> .List </xevm> // XEVM*
      <evm> .List </evm> // EVM*
      <height> 0 </height>
      <with> .Map </with> // Var -> StackLoc
      <b> // NOTE: mean break, but parser confuses with <br>
        <b-label> emptyLabel </b-label>
        <b-height> emptyHeight </b-height>
      </b>
      <labelTbl> .Map </labelTbl>
      <pos> 0 </pos>
    </T>

    syntax KResult ::= XEVM
                     | Label

//// XEVM

    rule <k> S:XEVM => . ... </k>
         <xevm> ... (.List => ListItem(S)) </xevm>

//// LLLEVM

    // L := V
    rule $mstore(L, V) => V ~> L ~> MSTORE

    rule $mload(L) => L ~> MLOAD

    rule $calldataload(L) => L ~> CALLDATALOAD
    rule $callvalue => CALLVALUE

    rule $eq(X, Y) => Y ~> X ~> EQ
    rule $add(X, Y) => Y ~> X ~> ADD

    rule $iszero(X) => X ~> ISZERO

    rule $stop => STOP

    // return mem[L..L+S]
    rule $return(L, S) => S ~> L ~> RETURN

    rule  $lt(X, Y) => Y ~> X ~>  LT
    rule  $gt(X, Y) => Y ~> X ~>  GT
    rule $slt(X, Y) => Y ~> X ~> SLT
    rule $sgt(X, Y) => Y ~> X ~> SGT

//// LLLExp

    rule N:Int => push(N)
    when -1 *Int (2 ^Int 255) <=Int N andBool N <Int (2 ^Int 256)

    rule <k> X:Id => DUP(H -Int L) ... </k>
         <height> H </height>
         <with> ... X |-> L ... </with>
    when H -Int L <=Int 16

    // X := V
    rule <k> $set(X, V) => V ~> SWAP(H -Int L) ~> POP ... </k>
         <height> H </height>
         <with> ... X |-> L ... </with>
    when H -Int L <=Int 16

    rule $pass => .

    rule $codelen => CODELEN

    rule $codeload(X) => $seq($codecopy(FREE_VAR_SPACE, X, 32), $mload(FREE_VAR_SPACE))

    // if C then T
    rule $if(C, T) => if(C, T, newLabel)    syntax KItem ::= "if" "(" LLLExp "," LLLExp "," Label ")"
    rule if(C, T, LEnd)
      => C
      ~> ISZERO ~> JUMPI(LEnd)
      ~> T
      ~> JUMPDEST(LEnd)
    /* TODO:DJ: clean semantics
      => $if(C, T, $pass)
    */

    // if C then T else F
    rule $if(C, T, F) => if(C, T, F, newLabel, newLabel)    syntax KItem ::= "if" "(" LLLExp "," LLLExp "," LLLExp "," Label "," Label ")"
    rule if(C, T, F, LMid, LEnd)
      => C
      ~> ISZERO ~> JUMPI(LMid)
      ~> T
      ~> JUMP(LEnd)
      ~> JUMPDEST(LMid)
      ~> F
      ~> JUMPDEST(LEnd)

    // for L = I; N times; do S
    rule $repeat(L, I, N:Int, S) => repeat(L, I, N, S, newLabel, newLabel)    syntax KItem ::= "repeat" "(" LLLExp "," LLLExp "," LLLExp "," LLLExp "," Label "," Label ")"
    rule <k> repeat(L, I, N:Int, S, LBegin, LEnd)
          => L
          ~> ctx(I, H +Int 1, W, BL, BH)
          ~> push(N) // NOTE: no need to consider zero case
          ~> DUP(2) ~> DUP(4) ~> MSTORE // L := I
          ~> ADD // I + N
          ~> JUMPDEST(LBegin)
          ~> ctx(S, H +Int 2, W, LEnd, H +Int 2)
          ~> DUP(2) ~> MLOAD // L
          ~> PUSH(1, 1) ~> ADD // L + 1
          ~> DUP(1) ~> DUP(4) ~> MSTORE // L := L + 1
          ~> DUP(2) ~> EQ ~> ISZERO ~> JUMPI(LBegin) // if(L =/= I + N) goto LBegin
          ~> JUMPDEST(LEnd)
          ~> POP ~> POP
         ... </k>
         <height> H </height>
         <with> W </with>
         <b-label> BL </b-label>
         <b-height> BH </b-height>
    when N >Int 0
    /* TODO:DJ: clean semantics
      L := I
      begin:
      S
      L := L + 1
      if (L != I + N) {
        goto begin
      }
      end:
      => $seq($mstore(L,I),
              JUMPDEST(begin),
              S,
              $mstore(L, $add($mload(L), 1)),
              $if($eq($mload(L), I + N),
                  $pass,
                  JUMP(begin)
                 ),
              JUMPDEST(end)
             )
    */

    rule <k> $break
          => pop(H -Int BH)
          ~> JUMP(BL)
         ... </k>
         <height> H </height>
         <b-label> BL </b-label>
         <b-height> BH </b-height>
    when BL =/=K emptyLabel andBool BH =/=K emptyHeight

    // let X = V in E
    rule <k> $with(X, V, E)
          => V
          ~> ctx(E, H +Int 1, W[X <- H], BL, BH)
          ~> #if valency(E) ==K 1 #then SWAP(1) #else . #fi
          ~> POP
         ... </k>
         <height> H </height>
         <with> W </with>
         <b-label> BL </b-label>
         <b-height> BH </b-height>

    rule $lll(S1, S2) => lll(S1, S2, newLabel, newLabel)    syntax KItem ::= "lll" "(" LLLExp "," LLLExp "," Label "," Label ")"
    rule <k> lll(S1, S2, LBegin, LEnd)
          => JUMP(LEnd)
          ~> JUMPDEST(LBegin)
          ~> ctx(S1, 0, .Map, emptyLabel, emptyHeight)
          ~> JUMPDEST(LEnd)
          ~> PUSH(LBegin) ~> PUSH(LEnd) ~> SUB
          ~> PUSH(LBegin)
          ~> S2
          ~> CODECOPY
          ~> PUSH(LBegin) ~> PUSH(LEnd) ~> SUB // TODO:DJ: optimize
         ...</k>
         <height> H </height>
         <with> W </with>

    rule $seq(S1, S2)
      => S1
      ~> #if valency(S1) ==K 1 #then POP #else . #fi
      ~> S2

    rule $assert(C)
      => C ~> assertTrue

    rule $uclamplt(X, UB) => X ~> UB ~> DUP(2) ~>  LT ~> assertTrue   /* X <  UB */
    rule $uclample(X, UB) => X ~> UB ~> DUP(2) ~>  GT ~> assertFalse  /* X <= UB */
    rule  $clamplt(X, UB) => X ~> UB ~> DUP(2) ~> SLT ~> assertTrue   /* X <  UB */
    rule  $clample(X, UB) => X ~> UB ~> DUP(2) ~> SGT ~> assertFalse  /* X <= UB */

    rule $uclampgt(X, LB) => X ~> LB ~> DUP(2) ~>  GT ~> assertTrue   /* X >  LB */
    rule $uclampge(X, LB) => X ~> LB ~> DUP(2) ~>  LT ~> assertFalse  /* X >= LB */
    rule  $clampgt(X, LB) => X ~> LB ~> DUP(2) ~> SGT ~> assertTrue   /* X >  LB */
    rule  $clampge(X, LB) => X ~> LB ~> DUP(2) ~> SLT ~> assertFalse  /* X >= LB */

    rule $uclamp(LB, X, UB)
      => LB ~> X ~> DUP(1) ~> UB ~> SWAP(1) ~>  GT ~> assertFalse /* X <= UB */
            ~> DUP(1) ~> SWAP(2) ~> SWAP(1) ~>  LT ~> assertFalse /* X >= LB */
    rule  $clamp(LB, X, UB)
      => LB ~> X ~> DUP(1) ~> UB ~> SWAP(1) ~> SGT ~> assertFalse /* X <= UB */
            ~> DUP(1) ~> SWAP(2) ~> SWAP(1) ~> SLT ~> assertFalse /* X >= LB */

    rule $clamp_nonzero(X)
      => X ~> DUP(1) ~> assertNonZero

    // TODO:DJ: viper could be wrong in  the order of arguments
    rule $sha3_32(X) => X ~> PUSH(1, FREE_VAR_SPACE) ~> MSTORE ~> PUSH(1, FREE_VAR_SPACE) ~> PUSH(1, 32) ~> SHA3

    rule  $ne(X, Y) => $iszero( $eq(X, Y))

    rule  $le(X, Y) => $iszero( $gt(X, Y))
    rule  $ge(X, Y) => $iszero( $lt(X, Y))
    rule $sle(X, Y) => $iszero($sgt(X, Y))
    rule $sge(X, Y) => $iszero($slt(X, Y))

    syntax Id ::= "_val" [token]
    // ceil32(x) = (x + 31) - ((x - 1) % 32)
    // TODO:DJ: equivalent and better? ((x + 31) / 32) * 32
    rule $ceil32(X) => $with(_val, X,
                             $sub($add(_val, 31),
                                  $mod($sub(_val, 1), 32)))

//// Valency

    syntax Int /* 0 or 1 */ ::= "valency" "(" LLLExp ")" [function]

    rule valency(_:Int) => 1

    rule valency($if(C, T, F)) => valency(T) when valency(C) ==K 1 andBool valency(T) ==K valency(F)
    rule valency($if(C, T   )) => valency(T) when valency(C) ==K 1 andBool valency(T) ==K 0

    rule valency($repeat(X, I, N:Int, S)) => 0 when valency(X) ==K 1 andBool N >Int 0 andBool valency(I) ==K 1 andBool valency(S) ==K 0

    rule valency($with(X, V, E)) => valency(E) when valency(V) ==K 1

    rule valency($seq(S1, S2)) => valency(S2)

    rule valency($lll(S1, S2)) => 1

    rule valency(_:Id) => 1

    rule valency($mstore(A,B)    ) => 0 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($mload(A)       ) => 1 when valency(A) ==K 1
    rule valency($calldataload(A)) => 1 when valency(A) ==K 1
    rule valency($callvalue      ) => 1
    rule valency($eq(A,B)        ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($add(A,B)       ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($iszero(A)      ) => 1 when valency(A) ==K 1
    rule valency($stop           ) => 0
    rule valency($return(A,B)    ) => 0 when valency(A) ==K 1 andBool valency(B) ==K 1

    rule valency($set(A,B)       ) => 0 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($pass           ) => 0
    rule valency($assert(A)      ) => 0 when valency(A) ==K 1

    rule valency($uclamplt(A,B)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($uclample(A,B)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency( $clamplt(A,B)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency( $clample(A,B)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($uclampgt(A,B)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($uclampge(A,B)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency( $clampgt(A,B)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency( $clampge(A,B)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1

    rule valency($uclamp(A,B,C)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1
    rule valency( $clamp(A,B,C)  ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1

//// Utils

    syntax Label ::= "newLabel" [function]
    rule newLabel => label(!N:Int)

    syntax Label ::= "emptyLabel" [function]
    rule emptyLabel => label(-1) // TODO:DJ: check if -1 doesn't conflict

    syntax Int ::= "emptyHeight" [function]
    rule emptyHeight => -1 // TODO:DJ: check if -1 doesn't conflict

    syntax KItem ::= "push" "(" Int ")"
                   | "push" "(" Int "," Int "," Bytes ")"
    rule push(N) => push(N modInt (2 ^Int 256)) // two's complement representation for negative numbers
    when -1 *Int (2 ^Int 255) <=Int N andBool N <Int 0
    //
    rule push(0) => PUSH(1, 0)
    rule push(N) => push(N, 0, .Bytes)
    when 0 <Int N andBool N <Int (2 ^Int 256)
    //
    rule push(0, S, B) => PUSH(S, B)
    rule push(N, S, B) => push(N /Int 256, S +Int 1, (N %Int 256) B)
    when N >Int 0

    syntax KItem ::= "pop" "(" Int ")"
    rule pop(N) => POP ~> pop(N -Int 1) when N >Int 0
    rule pop(0) => .

    syntax KItem ::= "height" "(" Int ")"
    rule <k> height(H) => . ... </k>
         <height> _ => H </height>

    syntax KItem ::= "with" "(" Map ")"
    rule <k> with(W) => . ... </k>
         <with> _ => W </with>

    syntax KItem ::= "break" "(" Label "," Int ")"
    rule <k> break(L, H) => . ... </k>
         <b-label> _ => L </b-label>
         <b-height> _ => H </b-height>

    syntax KItem ::= "ctx" "(" K "," Int "," Map "," Label "," Int ")"
    rule <k> ctx(K, H, W, BL, BH)
          => height(H) ~> with(W) ~> break(BL, BH)
          ~> K
          ~> height(H') ~> with(W') ~> break(BL', BH')
         ... </k>
         <height> H' </height>
         <with> W' </with>
         <b-label> BL' </b-label>
         <b-height> BH' </b-height>

    syntax KItem ::= "assertTrue"
    rule assertTrue => assertNonZero

    syntax KItem ::= "assertFalse"
    rule assertFalse => assertZero

    syntax KItem ::= "assertNonZero"
    rule assertNonZero
      => ISZERO ~> JUMPI(pc)

    syntax KItem ::= "assertZero"
    rule assertZero
      => JUMPI(pc)

    syntax Int ::= "FREE_VAR_SPACE" [function]
    rule FREE_VAR_SPACE => 192

    /* TODO:DJ: pre-occupied memory locations
    rule RESERVED_MEMORY => 320
    rule ADDRSIZE => 32
    rule MAXNUM => 64
    rule MINNUM => 96
    rule MAXDECIMAL => 128
    rule MINDECIMAL => 160
    rule FREE_VAR_SPACE => 192
    rule BLANK_SPACE => 224
    rule FREE_LOOP_INDEX => 256
    */

////
////
////

    syntax KItem ::= "xevm2evm"
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

    rule decode(.List) => .

    rule <k> decode(ListItem(C:EVM)   Code) => decode(Code) ... </k> <evm> ... (.List => ListItem(C)) </evm>

    rule <k> decode(ListItem(DUP(N))      Code) => decode(Code) ... </k> <evm> ... (.List => ListItem(decode1(DUP(N)))) </evm>
    rule <k> decode(ListItem(SWAP(N))     Code) => decode(Code) ... </k> <evm> ... (.List => ListItem(decode1(SWAP(N)))) </evm>
    rule <k> decode(ListItem(PUSH(N, B))  Code) => decodeBytes(B) ~> decode(Code) ... </k> <evm> ... (.List => ListItem(decode1(PUSH(N,B)))) </evm>

    rule <k> decode(ListItem(PUSH(L))     Code) => decodeInt(M[L]:>Int) ~> decode(                Code) ... </k> <labelTbl> M </labelTbl> when L in keys(M)
    rule <k> decode(ListItem(JUMP(L))     Code) => decodeInt(M[L]:>Int) ~> decode(ListItem(JUMP)  Code) ... </k> <labelTbl> M </labelTbl> when L in keys(M)
    rule <k> decode(ListItem(JUMPI(label(L)))    Code) => decodeInt(M[label(L)]:>Int) ~> decode(ListItem(JUMPI) Code) ... </k> <labelTbl> M </labelTbl> when label(L) in keys(M)
    rule <k> decode(ListItem(JUMPI(pc))   Code) => decode(ListItem(PC) ListItem(JUMPI) Code) ... </k>
    rule     decode(ListItem(JUMPDEST(_)) Code) =>                         decode(                Code)
    rule <k> decode(ListItem(CODELEN)     Code) => decodeInt(POS) ~>       decode(ListItem(JUMPI) Code) ... </k> <pos> POS </pos>

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
