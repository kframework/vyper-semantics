require "lll-syntax.k"
require "xevm-syntax.k"

module LLL-XEVM-SYNTAX
    imports LLL-SYNTAX
endmodule

module LLL-XEVM
    imports LLL-XEVM-SYNTAX
    imports XEVM-SYNTAX

    configuration <T>
      <k> $PGM:LLLExp </k>
      <xevm> .List </xevm> // XEVM*
      <height> 0 </height>
      <with> .Map </with> // Var -> StackLoc
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

//TODO:
//  rule $codelen =>
//  rule $codeload =>

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
          ~> ctx(I, H +Int 1, W)
          ~> push(N) // NOTE: no need to consider zero case
          ~> DUP(2) ~> DUP(4) ~> MSTORE // L := I
          ~> ADD // I + N
          ~> JUMPDEST(LBegin)
          ~> ctx(S, H +Int 2, W) // TODO:DJ: break
          ~> DUP(2) ~> MLOAD // L
          ~> PUSH(1, 1) ~> ADD // L + 1
          ~> DUP(1) ~> DUP(4) ~> MSTORE // L := L + 1
          ~> DUP(2) ~> EQ ~> ISZERO ~> JUMPI(LBegin) // if(L =/= I + N) goto LBegin
          ~> JUMPDEST(LEnd)
          ~> POP ~> POP
         ... </k>
         <height> H </height>
         <with> W </with>
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

//  rule $break( // TODO:

    // let X = V in E
    rule <k> $with(X, V, E)
          => V
          ~> ctx(E, H +Int 1, W[X <- H])
          ~> #if valency(E) ==K 1 #then SWAP(1) #else . #fi
          ~> POP
         ... </k>
         <height> H </height>
         <with> W </with>

    rule $lll(S1, S2) => lll(S1, S2, newLabel, newLabel)    syntax KItem ::= "lll" "(" LLLExp "," LLLExp "," Label "," Label ")"
    rule <k> lll(S1, S2, LBegin, LEnd)
          => JUMP(LEnd)
          ~> JUMPDEST(LBegin)
          ~> ctx(S1, 0, .Map)
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

    syntax KItem ::= "height" "(" Int ")"
    rule <k> height(H) => . ... </k>
         <height> _ => H </height>

    syntax KItem ::= "with" "(" Map ")"
    rule <k> with(W) => . ... </k>
         <with> _ => W </with>

    syntax KItem ::= "ctx" "(" K "," Int "," Map ")"
    rule <k> ctx(K, H, W)
          => height(H) ~> with(W)
          ~> K
          ~> height(H') ~> with(W')
         ... </k>
         <height> H' </height>
         <with> W' </with>

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

endmodule
