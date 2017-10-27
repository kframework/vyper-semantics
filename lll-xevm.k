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

////

    rule <k> S:XEVM => . ... </k>
         <xevm> ... (.List => ListItem(S)) </xevm>

////

    // L := V
    rule $mstore(L, V) => V ~> L ~> MSTORE

    rule $mload(L) => L ~> MLOAD

    rule $calldataload(L) => L ~> CALLDATALOAD
    rule $callvalue => CALLVALUE

    rule $eq(X, Y) => Y ~> X ~> EQ

    rule $iszero(X) => X ~> ISZERO

    rule $stop => STOP

    // return mem[L..L+S]
    rule $return(L, S) => S ~> L ~> RETURN

////

    rule N:Int => push(N)
    when -1 *Int (2 ^Int 255) <=Int N andBool N <Int (2 ^Int 256)

/*
    rule <k> $var(X) => DUP(H - L) ... </k>
         <height> H </height>
         <with> ... X |-> L ... </with>
    when H - L <= 16

    // X := V
    rule <k> $set(X, V) => V ~> SWAP(H - L) ~> POP ... </k>
         <height> H </height>
         <with> ... X |-> L ... </with>
    when H - L <= 16
*/

    rule $pass => .

    // if C then T
    rule $if(C, T) => if(C, T, newLabel)
    syntax KItem ::= if(LLLExp, LLLExp, K) [seqstrict(3)]
    rule if(C, T, LEnd:Label)
      => C
      ~> ISZERO ~> JUMPI(LEnd)
      ~> T
      ~> JUMPDEST(LEnd)

/*
    // if C then T else F
    rule $if(C, T, F) => if(C, T, F, newLabel, newLabel)
    rule $if(C, T, F, LMid, LEnd)
      => C
      ~> ISZERO ~> JUMPI(LMid)
      ~> T
      ~> JUMP(LEnd)
      ~> JUMPDEST(LMid)
      ~> F
      ~> JUMPDEST(LEnd)

    // let X = V in E
    rule <k>
         $with(X, V, E)
      => V
      ~> ctx(E, H + 1, W[X <- H])
      ~> #if valency(E) == 0 #then SWAP(1) #else . #fi
      ~> POP
         ...</k>
         <height> H </height>
         <with> W </with>
*/

    rule $lll(S1, S2) => lll(S1, S2, newLabel, newLabel)
    syntax KItem ::= lll(LLLExp, LLLExp, K, K) [seqstrict(3,4)]
    rule <k> lll(S1, S2, LBegin:Label, LEnd:Label)
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
//    ~> #if valency(S1) == 1 #then POP #else . #fi // TODO
      ~> S2

    rule $assert(C)
      => C
      ~> ISZERO ~> JUMPI(pc)

////

    syntax KItem ::= "newLabel"
    rule newLabel => label(!N:Int)

    syntax KItem ::= push(Int)
    rule push(0) => PUSH(1, 0)
    rule push(N) => pushAux(N, 0, .Bytes)
    when 0 <Int N andBool N <Int (2 ^Int 256)
    //
    rule push(N) => push(N modInt (2 ^Int 256)) // two's complement representation for negative numbers
    when -1 *Int (2 ^Int 255) <=Int N andBool N <Int 0

    syntax KItem ::= pushAux(Int, Int, Bytes)
    rule pushAux(0, S, B) => PUSH(S, B)
    rule pushAux(N, S, B) => pushAux(N /Int 256, S +Int 1, (N %Int 256) B)
    when N >Int 0

    syntax KItem ::= height(Int)
    rule <k> height(H) => . ... </k>
         <height> _ => H </height>

    syntax KItem ::= with(Map)
    rule <k> with(W) => . ... </k>
         <with> _ => W </with>

    syntax KItem ::= ctx(K, Int, Map)
    rule <k> ctx(K, H, W)
          => height(H) ~> with(W)
          ~> K
          ~> height(H') ~> with(W')
         ... </k>
         <height> H' </height>
         <with> W' </with>

endmodule
