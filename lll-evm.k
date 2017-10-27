require "lll-evm-interface.k"
require "viper-config.k"

module LLL-EVM
    imports LLL-EVM-INTERFACE
    imports LLL-SYNTAX
    imports EVM-SYNTAX
    imports VIPER-CONFIG

    rule <k> S:XEVM => . ... </k>
         <xevm> ... (. => S) </xevm>

////

    // L := V
    rule $mstore(L,V) => V ~> L ~> MSTORE

    rule $mload(L) => L ~> MLOAD

////

    rule N:Int => push(N)
    when -2^255 <= N < 2^256

    rule <k> $var(X) => DUP(H - L) ... </k>
         <height> H </height>
         <with> ... X |-> L ... </with>
    when H - L <= 16

    // X := V
    rule <k> $set(X,V) => V ~> SWAP(H - L) ~> POP ... </k>
         <height> H </height>
         <with> ... X |-> L ... </with>
    when H - L <= 16

    rule $pass => .

    // if C then T
    rule $if(C,T) => $if(C,T;mk_label)
    rule $if(C,T;LEnd)
      => C
      ~> ISZERO ~> JUMPI(LEnd)
      ~> T
      ~> JUMPDEST(LEnd)

    // if C then T else F
    rule $if(C,T,F) => if(C,T,F;mk_label;mk_label)
    rule $if(C,T,F;LMid,LEnd)
      => C
      ~> ISZERO ~> JUMPI(LMid)
      ~> T
      ~> JUMP(LEnd)
      ~> JUMPDEST(LMid)
      ~> F
      ~> JUMPDEST(LEnd)

    // let X = V in E
    rule <k>
         $with(X,V,E)
      => V
      ~> ctx(E, H + 1, W[X <- H])
      ~> #if valency(E) == 0 #then SWAP(1) #else . #fi
      ~> POP
         ...</k>
         <height> H </height>
         <with> W </with>

    rule $lll(S1,S2) => $lll(S1,S2;mk_label;mk_label)
    rule <k>
         $lll(S1,S2;LBegin,LEnd)
      => JUMP(LEnd)
      ~> JUMPDEST(LBegin)
      ~> ctx(S1, 0, .Map)
      ~> JUMPDEST(LEnd)
      ~> PUSH(LBegin) ~> PUSH(LEnd) ~> SUB
      ~> PUSH(LBegin)
      ~> S2
      ~> CODECOPY
      ~> PUSH(LBegin) ~> PUSH(LEnd) ~> SUB
         ...</k>
         <height> H </height>
         <with> W </with>

    rule $seq(S1 S2 Ss)
      => S1
      ~> #if valency(S1) == 1 #then POP #else . #fi
      ~> $seq(S2 Ss)
    rule $seq(S .LLLExps) => S

    rule $assert(C)
      => C
      ~> ISZERO ~> JUMPI(PC)


////

    rule push(N)
      => push(N % 2^256) // two's complement representation for negative numbers
    when -2^255 <= N < 0

    rule push(0)
      => PUSH(1,0)

    rule push(N)
      => let b = num_to_bytearray(N) in
         PUSH(size(b), b)
    when 0 < N < 2^256

    rule num_to_bytearray(N)
      => let f(n,b) =
           if n = 0 then b
           else f(n / 256, (n % 256) :: b)
         in
         f(N,nil)
    when N > 0

    rule <k> height(H) => . ... </k>
         <height> _ => H </height>

    rule <k> with(W) => . ... </k>
         <with> _ => W </with>

    rule <k>
         ctx(K,H,W)
      =>
         height(H) ~> with(W)
      ~> K
      ~> height(H') ~> with(W')
         ...</k>
         <height> H' </height>
         <with> W' </with>



endmodule
