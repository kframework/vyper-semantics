require "lll-xevm-interface.k"
require "lll-syntax.k"
require "xevm-syntax.k"
require "lll-evm-config.k"

module LLL-XEVM
    imports LLL-XEVM-INTERFACE

    imports LLL-EVM-CONFIG

//  imports LLL-SYNTAX
    imports XEVM-SYNTAX

    syntax KResult ::= XEVM
                     | Label

//// XEVM

    rule <k> S:XEVM => . ... </k>
         <xevm> ... (.List => ListItem(S)) </xevm>

//// LLLEVM

    rule $stop                                         =>                                    STOP
    rule $add           ( A , B )                      => do( B   A )                     ~> ADD
    rule $mul           ( A , B )                      => do( B   A )                     ~> MUL
    rule $sub           ( A , B )                      => do( B   A )                     ~> SUB
    rule $div           ( A , B )                      => do( B   A )                     ~> DIV
    rule $sdiv          ( A , B )                      => do( B   A )                     ~> SDIV
    rule $mod           ( A , B )                      => do( B   A )                     ~> MOD
    rule $smod          ( A , B )                      => do( B   A )                     ~> SMOD
    rule $addmod        ( A , B , C )                  => do( C   B   A )                 ~> ADDMOD
    rule $mulmod        ( A , B , C )                  => do( C   B   A )                 ~> MULMOD
    rule $exp           ( A , B )                      => do( B   A )                     ~> EXP
    rule $signextend    ( A , B )                      => do( B   A )                     ~> SIGNEXTEND
    rule $lt            ( A , B )                      => do( B   A )                     ~> LT
    rule $gt            ( A , B )                      => do( B   A )                     ~> GT
    rule $slt           ( A , B )                      => do( B   A )                     ~> SLT
    rule $sgt           ( A , B )                      => do( B   A )                     ~> SGT
    rule $eq            ( A , B )                      => do( B   A )                     ~> EQ
    rule $iszero        ( A )                          => do( A )                         ~> ISZERO
    rule $and           ( A , B )                      => do( B   A )                     ~> AND
    rule $or            ( A , B )                      => do( B   A )                     ~> EVMOR
    rule $xor           ( A , B )                      => do( B   A )                     ~> XOR
    rule $not           ( A )                          => do( A )                         ~> NOT
    rule $byte          ( A , B )                      => do( B   A )                     ~> BYTE
    rule $sha3          ( A , B )                      => do( B   A )                     ~> SHA3
    rule $address                                      =>                                    ADDRESS
    rule $balance                                      =>                                    BALANCE
    rule $origin                                       =>                                    ORIGIN
    rule $caller                                       =>                                    CALLER
    rule $callvalue                                    =>                                    CALLVALUE
    rule $calldataload  ( A )                          => do( A )                         ~> CALLDATALOAD
    rule $calldatasize                                 =>                                    CALLDATASIZE
    rule $calldatacopy  ( A , B , C )                  => do( C   B   A )                 ~> CALLDATACOPY
    rule $codesize                                     =>                                    CODESIZE
    rule $codecopy      ( A , B , C )                  => do( C   B   A )                 ~> CODECOPY
    rule $gasprice                                     =>                                    GASPRICE
    rule $extcodesize   ( A )                          => do( A )                         ~> EXTCODESIZE
    rule $extcodecopy   ( A , B , C , D )              => do( D   C   B   A )             ~> EXTCODECOPY
    rule $blockhash     ( A )                          => do( A )                         ~> BLOCKHASH
    rule $coinbase                                     =>                                    COINBASE
    rule $timestamp                                    =>                                    TIMESTAMP
    rule $number                                       =>                                    NUMBER
    rule $difficulty                                   =>                                    DIFFICULTY
    rule $gaslimit                                     =>                                    GASLIMIT
    rule $pop           ( A )                          => do( A )                         ~> POP
    rule $mload         ( A )                          => do( A )                         ~> MLOAD
    rule $mstore        ( A , B )                      => do( B   A )                     ~> MSTORE
    rule $mstore8       ( A , B )                      => do( B   A )                     ~> MSTORE8
    rule $sload         ( A )                          => do( A )                         ~> SLOAD
    rule $sstore        ( A , B )                      => do( B   A )                     ~> SSTORE
  //rule $jump          ( A )                          => do( A )                         ~> JUMP
  //rule $jumpi         ( A , B )                      => do( B   A )                     ~> JUMPI
  //rule $pc                                           =>                                    PC
    rule $msize                                        =>                                    MSIZE
    rule $gas                                          =>                                    GAS
  //rule $jumpdest                                     =>                                    JUMPDEST
    rule $log0          ( A , B )                      => do( B   A )                     ~> LOG0
    rule $log1          ( A , B , C )                  => do( C   B   A )                 ~> LOG1
    rule $log2          ( A , B , C , D )              => do( D   C   B   A )             ~> LOG2
    rule $log3          ( A , B , C , D , E )          => do( E   D   C   B   A )         ~> LOG3
    rule $log4          ( A , B , C , D , E , F )      => do( F   E   D   C   B   A )     ~> LOG4
    rule $create        ( A , B , C )                  => do( C   B   A )                 ~> CREATE
    rule $call          ( A , B , C , D , E , F , G )  => do( G   F   E   D   C   B   A ) ~> CALL
    rule $callcode      ( A , B , C , D , E , F , G )  => do( G   F   E   D   C   B   A ) ~> CALLCODE
    rule $return        ( A , B )                      => do( B   A )                     ~> RETURN
    rule $delegatecall  ( A , B , C , D , E , F )      => do( F   E   D   C   B   A )     ~> DELEGATECALL
    rule $callblackbox  ( A , B , C , D , E , F , G )  => do( G   F   E   D   C   B   A ) ~> CALLBLACKBOX
    rule $invalid                                      =>                                    INVALID
    rule $suicide       ( A )                          => do( A )                         ~> SUICIDE
    rule $selfdestruct  ( A )                          => do( A )                         ~> SELFDESTRUCT

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
          ~> BLANK(LBegin)
          ~> LLLBEGIN
          ~> ctx(S1, 0, .Map, emptyLabel, emptyHeight)
          ~> LLLEND
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

    rule $uclamplt(X, UB) => do(X UB) ~> DUP(2) ~>  LT ~> assertTrue   /* X <  UB */
    rule $uclample(X, UB) => do(X UB) ~> DUP(2) ~>  GT ~> assertFalse  /* X <= UB */
    rule  $clamplt(X, UB) => do(X UB) ~> DUP(2) ~> SLT ~> assertTrue   /* X <  UB */
    rule  $clample(X, UB) => do(X UB) ~> DUP(2) ~> SGT ~> assertFalse  /* X <= UB */

    rule $uclampgt(X, LB) => do(X LB) ~> DUP(2) ~>  GT ~> assertTrue   /* X >  LB */
    rule $uclampge(X, LB) => do(X LB) ~> DUP(2) ~>  LT ~> assertFalse  /* X >= LB */
    rule  $clampgt(X, LB) => do(X LB) ~> DUP(2) ~> SGT ~> assertTrue   /* X >  LB */
    rule  $clampge(X, LB) => do(X LB) ~> DUP(2) ~> SLT ~> assertFalse  /* X >= LB */

    rule $uclamp(LB, X, UB)
      => do(LB X) ~> DUP(1) ~> doh(UB,3) ~> SWAP(1) ~>  GT ~> assertFalse /* X <= UB */
                    ~> DUP(1) ~> SWAP(2) ~> SWAP(1) ~>  LT ~> assertFalse /* X >= LB */
    rule  $clamp(LB, X, UB)
      => do(LB X) ~> DUP(1) ~> doh(UB,3) ~> SWAP(1) ~> SGT ~> assertFalse /* X <= UB */
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

    rule valency($if(C, T, F)) => valency(T) when valency(C) ==K 1 andBool valency(T) ==K valency(F)
    rule valency($if(C, T   )) => valency(T) when valency(C) ==K 1 andBool valency(T) ==K 0

    rule valency($repeat(X, I, N:Int, S)) => 0 when valency(X) ==K 1 andBool N >Int 0 andBool valency(I) ==K 1 andBool valency(S) ==K 0

    rule valency($with(X, V, E)) => valency(E) when valency(V) ==K 1

    rule valency($seq(S1, S2)) => valency(S2)

    rule valency($lll(_, _)) => 1

    rule valency(_:Int) => 1
    rule valency(_:Id) => 1

    rule valency($break           ) => 0
    rule valency($set(A,B)        ) => 0 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($pass            ) => 0
    rule valency($assert(A)       ) => 0 when valency(A) ==K 1

    rule valency($ne (A,B)        ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($le (A,B)        ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($ge (A,B)        ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($sle(A,B)        ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($sge(A,B)        ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1

    rule valency($uclamplt(A,B)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($uclample(A,B)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency( $clamplt(A,B)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency( $clample(A,B)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($uclampgt(A,B)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($uclampge(A,B)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency( $clampgt(A,B)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency( $clampge(A,B)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1

    rule valency($uclamp(A,B,C)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1
    rule valency( $clamp(A,B,C)   ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1

    rule valency($clamp_nonzero(A)) => 1 when valency(A) ==K 1
    rule valency($ceil32 (A)      ) => 1 when valency(A) ==K 1
    rule valency($sha3_32(A)      ) => 1 when valency(A) ==K 1
    rule valency($codelen         ) => 1
    rule valency($codeload(A)     ) => 1 when valency(A) ==K 1


    rule valency($mstore(A,B)     ) => 0 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($mload(A)        ) => 1 when valency(A) ==K 1
    rule valency($calldataload(A) ) => 1 when valency(A) ==K 1
    rule valency($callvalue       ) => 1
    rule valency($eq(A,B)         ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($add(A,B)        ) => 1 when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($iszero(A)       ) => 1 when valency(A) ==K 1
    rule valency($stop            ) => 0
    rule valency($return(A,B)     ) => 0 when valency(A) ==K 1 andBool valency(B) ==K 1

    rule valency($stop                                         )  =>   0
    rule valency($add           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($mul           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($sub           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($div           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($sdiv          ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($mod           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($smod          ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($addmod        ( A , B , C )                  )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1
    rule valency($mulmod        ( A , B , C )                  )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1
    rule valency($exp           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($signextend    ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($lt            ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($gt            ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($slt           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($sgt           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($eq            ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($iszero        ( A )                          )  =>   1   when valency(A) ==K 1
    rule valency($and           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($or            ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($xor           ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($not           ( A )                          )  =>   1   when valency(A) ==K 1
    rule valency($byte          ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($sha3          ( A , B )                      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($address                                      )  =>   1
    rule valency($balance                                      )  =>   1
    rule valency($origin                                       )  =>   1
    rule valency($caller                                       )  =>   1
    rule valency($callvalue                                    )  =>   1
    rule valency($calldataload  ( A )                          )  =>   1   when valency(A) ==K 1
    rule valency($calldatasize                                 )  =>   1
    rule valency($calldatacopy  ( A , B , C )                  )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1
    rule valency($codesize                                     )  =>   1
    rule valency($codecopy      ( A , B , C )                  )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1
    rule valency($gasprice                                     )  =>   1
    rule valency($extcodesize   ( A )                          )  =>   1   when valency(A) ==K 1
    rule valency($extcodecopy   ( A , B , C , D )              )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1 andBool valency(D) ==K 1
    rule valency($blockhash     ( A )                          )  =>   1   when valency(A) ==K 1
    rule valency($coinbase                                     )  =>   1
    rule valency($timestamp                                    )  =>   1
    rule valency($number                                       )  =>   1
    rule valency($difficulty                                   )  =>   1
    rule valency($gaslimit                                     )  =>   1
    rule valency($pop           ( A )                          )  =>   0   when valency(A) ==K 1
    rule valency($mload         ( A )                          )  =>   1   when valency(A) ==K 1
    rule valency($mstore        ( A , B )                      )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($mstore8       ( A , B )                      )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($sload         ( A )                          )  =>   1   when valency(A) ==K 1
    rule valency($sstore        ( A , B )                      )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1
  //rule valency(JUMP                                          )  =>   0
  //rule valency(JUMPI                                         )  =>   0
  //rule valency(PC                                            )  =>   1
    rule valency($msize                                        )  =>   1
    rule valency($gas                                          )  =>   1
  //rule valency(JUMPDEST                                      )  =>   0
  //rule valency(PUSH...                                       )  =>   1
  //rule valency(DUP...                                        )  =>   1
  //rule valency(SWAP...                                       )  =>   1
    rule valency($log0          ( A , B )                      )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($log1          ( A , B , C )                  )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1
    rule valency($log2          ( A , B , C , D )              )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1 andBool valency(D) ==K 1
    rule valency($log3          ( A , B , C , D , E )          )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1 andBool valency(D) ==K 1 andBool valency(E) ==K 1
    rule valency($log4          ( A , B , C , D , E , F )      )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1 andBool valency(D) ==K 1 andBool valency(E) ==K 1 andBool valency(F) ==K 1
    rule valency($create        ( A , B , C )                  )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1
    rule valency($call          ( A , B , C , D , E , F , G )  )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1 andBool valency(D) ==K 1 andBool valency(E) ==K 1 andBool valency(F) ==K 1 andBool valency(G) ==K 1
    rule valency($callcode      ( A , B , C , D , E , F , G )  )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1 andBool valency(D) ==K 1 andBool valency(E) ==K 1 andBool valency(F) ==K 1 andBool valency(G) ==K 1
    rule valency($return        ( A , B )                      )  =>   0   when valency(A) ==K 1 andBool valency(B) ==K 1
    rule valency($delegatecall  ( A , B , C , D , E , F )      )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1 andBool valency(D) ==K 1 andBool valency(E) ==K 1 andBool valency(F) ==K 1
    rule valency($callblackbox  ( A , B , C , D , E , F , G )  )  =>   1   when valency(A) ==K 1 andBool valency(B) ==K 1 andBool valency(C) ==K 1 andBool valency(D) ==K 1 andBool valency(E) ==K 1 andBool valency(F) ==K 1 andBool valency(G) ==K 1
    rule valency($invalid                                      )  =>   0
    rule valency($suicide       ( A )                          )  =>   0   when valency(A) ==K 1
    rule valency($selfdestruct  ( A )                          )  =>   0   when valency(A) ==K 1

//// Utils

    syntax Label ::= "newLabel" [function]
    rule newLabel => label(!N:Int)

//  syntax Label ::= "emptyLabel" [function]
    rule emptyLabel => label(-1) // TODO:DJ: check if -1 doesn't conflict

//  syntax Int ::= "emptyHeight" [function]
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

    // TODO:DJ: cleaner?
    syntax Ls ::= List{LLLExp,""}
    syntax KItem ::= "do" "(" Ls ")"
                   | "do" "(" Ls "," Int ")"
                   | "doh" "(" Ls "," Int ")"
    rule <k> do(Es) => do(Es, H) ... </k>
         <height> H </height>
    rule <k> do(E Es, H) => ctx(E, H, W, BL, BH) ~> do(Es, H +Int 1) ... </k>
         <with> W </with>
         <b-label> BL </b-label>
         <b-height> BH </b-height>
    rule do(.Ls, _) => .
    rule <k> doh(Es, HInc) => do(Es, H +Int HInc) ... </k>
         <height> H </height>

endmodule
