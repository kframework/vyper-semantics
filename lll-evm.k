require "lll-evm-interface.k"
require "viper-config.k"

module LLL-EVM
    imports LLL-EVM-INTERFACE
    imports LLL-SYNTAX
    imports EVM-SYNTAX
    imports VIPER-CONFIG

    rule $mstore(L,V) // L := V
      => V L MSTORE

    rule $mload(L)
      => L MLOAD

////

    rule N:Int
      => push(N)
    when -2^255 <= N < 2^256

    rule $var(X)
      => DUP(H - W[X])
         <height> H </height>
         <with> W </with>
    when H - W[X] <= 16

    rule $set(X,V) // X := V
      => V SWAP(H - W[X]) POP

    rule $pass
      => .

    rule $if(C,T) // if C then T
      => let end_label = mk_label() in
         C
         ISZERO JUMPI(end_label)
         T
         JUMPDEST(end_label)

    rule $if(C,T,F) // if C then T else F
      => let mid_label = mk_label() in
         let end_label = mk_label() in
         C
         ISZERO JUMPI(mid_label)
         T
         JUMP(end_label)
         JUMPDEST(mid_label)
         F
         JUMPDEST(end_label)

    rule $with(X,V,E) // let X = V in E
      => V
         E // TODO: with height update
         <height> H </height>
         <with> X |-> (_ => H) </with>
         // TODO: fix

    rule $lll(S1,S2)
      => let l_begin = mk_label() in
         let l_end   = mk_label() in
         JUMP(l_end)
         JUMPDEST(l_begin)
         S1 // clean env
         JUMPDEST(l_end)
         PUSH(l_begin) PUSH(l_end) SUB
         PUSH(l_begin)
         S2
         CODECOPY
         PUSH(l_begin) PUSH(l_end) SUB

    rule $seq(S1,S2)
      => S1
         POP // TODO: if needed
         S2

    rule $assert(C)
      => C
         ISZERO JUMPI(PC)


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



endmodule
