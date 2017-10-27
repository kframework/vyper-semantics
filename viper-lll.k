require "viper-lll-interface.k"
require "viper-config.k"
require "utils.k"

module VIPER-LLL
    imports VIPER-LLL-INTERFACE
    imports VIPER-SYNTAX
    imports LLL-SYNTAX
    imports VIPER-CONFIG
    imports UTILS

 // syntax KItem     ::= "#compileViperToLLL" "(" Pgm ")"
 // -----------------------------------------------------
    rule #compileViperToLLL(%pgm(GS, INIT, DEFS)) => #pushCodeToStack
                                                  ~> #resolveGlobals(GS)
                                                  ~> #resolveInit(INIT)
                                                  ~> #returnCode
                                                  ~> #appendWithSeq

    rule #compileViperToLLL(%pgm(GS, DEFS)) => #resolveGlobals(GS)


    syntax TypedAddr ::= "@taddr" "(" Type "," Int "," Bool /*mutable*/ ")"
                       | "@taddr" "(" Map ")"    // struct
    syntax KItem     ::= "#resolveGlobals" "(" Globals ")"
 // ------------------------------------------------------
    rule #resolveGlobals(.Globals) => .

    rule <k> #resolveGlobals(%svdecl(NAME, T, _) GS) => #resolveGlobals(GS) ... </k>
         <global> GLOBAL => GLOBAL[%svar(NAME) <- @taddr(T, LOC, true)] </global>
         <nextStorage> LOC => LOC +Int 1 </nextStorage>


    syntax KItem     ::= "#resolveInitFunc" "(" Def ")"
 // ---------------------------------------------------
    rule <k> #resolveInit(%fdecl(DECS, __init__, PARAMS, T, STMTS)) => #pushCodeToStack
                                                                    ~> #copyInput(__init__, PARAMS)
                                                                    ~> #checkDecorators(DECS)
                                                                    ~> #fillParams(PARAMS, 0, true)
                                                                    ~> #returnCode
                                                                    ~> #appendWithSeq
                                                                    ~> #exception("Debug")
                                                                    ~> #env(ENV, M) ...
         </k>
         <lll> CODE => #extLLL(CODE, $seq(#initializer_lll);.LLLExps) </lll>
         <env> ENV </env>
         <nextMem> M </nextMem>


    syntax KItem     ::= "#resolveRegularFunc" "(" Def ")"
 // ------------------------------------------------------
    rule <k> #resolveFunc(%fdecl(DECS, NAME, PARAMS, T, STMTS)) => #pushCodeToStack
                                                                ~> #copyInput(NAME, PARAMS)
                                                                ~> #checkDecorators(DECS)
                                                                ~> #fillParams(PARAMS, 0, false)
                                                                ~> #resolveStmts(STMTS)
                                                                ~> #returnCode
                                                                ~> #appendWithSeq
                                                                ~> #env(ENV, M) ...
         </k>
         <env> ENV </env>
         <nextMem> M </nextMem>


    syntax KItem     ::= "#resolveStmts"       "(" Stmts ")"
    syntax KItem     ::= "#resolveStmtsHelper" "(" Stmts ")"
    syntax KItem     ::= "#resolveStmt"        "(" Stmt ")"
 // --------------------------------------------------------
    rule #resolveStmts(.Stmts) => .

    rule #resolveStmts(SS) => #pushCodeToStack
                           ~> #resolveStmtsHelper(SS)
                           ~> #returnCode
                           ~> #appendWithSeq

    rule #resolveStmtsHelper(.Stmts) => .

    rule #resolveStmtsHelper(S SS) => #resolveStmt(S) ~> #resolveStmtsHelper(SS)


 //   syntax KItem     ::= "#resolveExpr" (" Expr ")"
 // -----------------------------------------------


    syntax KItem     ::= "#copyInput" "(" Id "," Params ")"
 // -------------------------------------------------------
    rule <k> #copyInput(__init__, PARAMS) => . ... </k>
         <lll> CODE => #extLLL(CODE, $codecopy(#reservedMemPos, ~codelen, #paramsSize(PARAMS))) </lll>
         <nextMem> M => M +Int #paramsSize(PARAMS) </nextMem>

    rule <k> #copyInput(NAME, PARAMS) => . ... </k>
         <lll> CODE => #extLLL(CODE, $calldatacopy(#reservedMemPos, 4, #paramsSize(PARAMS))) </lll>
         <nextMem> M => M +Int #paramsSize(PARAMS) </nextMem>
      requires NAME =/=K __init__


    syntax KItem     ::= "#checkDecorators" "(" Decorators ")"
    syntax KItem     ::= "#checkConstant"   "(" Decorators ")"
    syntax KItem     ::= "#checkPayable"    "(" Decorators ")"
    syntax KItem     ::= "#checkInternal"   "(" Decorators ")"
 // ----------------------------------------------------------
    rule #checkDecorators(DECS) => #checkConstant(DECS) ~> #checkPayable(DECS) ~> #checkInternal(DECS)

    rule <k> #checkConstant(DECS) => . ... </k>
         <constant> _ => true </constant>
      requires #inDecorators(%@constant, DECS)

    rule <k> #checkConstant(DECS) => . ... </k>
         <constant> _ => false </constant>
      requires notBool #inDecorators(%@constant, DECS)

    rule <k> #checkPayable(DECS) => . ... </k>
         <payable> _ => true </payable>
      requires #inDecorators(%@payable, DECS)

    rule <k> #checkPayable(DECS) => . ... </k>
         <lll> CODE => #extLLL(CODE, $assert($iszero(callvalue))) </lll>
         <payable> _ => false </payable>
      requires notBool #inDecorators(%@payable, DECS)

    rule <k> #checkInternal(DECS) => . ... </k>
         <lll> CODE => #extLLL(CODE, $assert($eq(caller, address))) </lll>
      requires #inDecorators(%@internal, DECS)

    rule #checkInternal(DECS) => .
      requires notBool #inDecorators(%@internal, DECS)


    syntax KItem    ::= "#fillParams" "(" Params "," Int /*data pos*/ "," Bool")"
    syntax KItem    ::= "#fillParam"  "(" Param  "," Int "," Bool ")"
 // -------------------------------------------------------------------------------------
    rule #fillParams(.Params, _, _) => .

    rule #fillParams(P PS, DATAPOS, ISINIT)
             => #fillParam(P, DATAPOS, ISINIT) ~> #fillParams(PS, DATAPOS +Int #paramSize(P), ISINIT)

    rule <k> #fillParam(%param(NAME, %bytes(L)), DATAPOS, ISINIT) => . ... </k>
         <lll> CODE => #extLLL(CODE, #mkClamper(%bytes(L), DATAPOS, M, ISINIT)) </lll>
         <env> ENV => #allocVar(%var(NAME), %bytes(L), M, ENV, false)</env>
         <nextMem> M => M +Int #size(%bytes(L)) </nextMem>

    rule <k> #fillParam(%param(NAME, T), DATAPOS, ISINIT) => . ... </k>
         <lll> CODE => #extLLL(CODE, #mkClamper(T, DATAPOS, M, ISINIT)) </lll>
         <env> ENV => #allocVar(%var(NAME), T, #reservedMemPos +Int DATAPOS, ENV, false) </env>
         <nextMem> M </nextMem>
      requires notBool isByteArrayType(T)


    syntax KItem    ::= "#pushCodeToStack"
 // --------------------------------------
    rule <k> #pushCodeToStack => . ... </k>
         <lll> CODE => .LLLExps </lll>
         <lllCodeStack> .List => ListItem(CODE) ...</lllCodeStack>


    syntax KItem    ::= "#returnCode"
 // ---------------------------------
    rule <k> #returnCode => SUBCODE ... </k>
         <lll> SUBCODE => CODE </lll>
         <lllCodeStack> ListItem(CODE) => .List ...</lllCodeStack>


    syntax KItem    ::= "#appendWithSeq"
 // ------------------------------------
    rule <k> SUBCODE:LLLExps ~> #appendWithSeq => . ... </k>
         <lll> CODE => #extLLL(CODE, $seq(SUBCODE);.LLLExps) </lll>


//////////////////////////////////////////////////////////////////////////////
// Helper functions
//////////////////////////////////////////////////////////////////////////////


    syntax Map ::= "#allocVar" "(" Var "," Type "," Int "," Map "," Bool /*mutable*/ ")"    [function]
    syntax Map ::= "#flattenStruct" "(" Var "," VarDecls "," Int "," Map "," Bool ")"       [function]
 // --------------------------------------------------------------------------------------------------
    rule #allocVar(V, %struct(VARDECLS), LOC, M, ISMUTABLE) => #flattenStruct(V, VARDECLS, LOC, M, ISMUTABLE)

    rule #allocVar(V, T, LOC, M, ISMUTABLE) => M[V <- @taddr(T, LOC, ISMUTABLE)]    requires notBool isStructType(T)

    rule #flattenStruct(V, .VarDecls, LOC, M, ISMUTABLE) => M

    rule #flattenStruct(V, %vdecl(NAME, T) VS, LOC, M, ISMUTABLE)
             => #flattenStruct(V, VS, LOC +Int #size(T), #allocVar(%mem(V, NAME), T, LOC, M, ISMUTABLE), ISMUTABLE)


    syntax Int       ::= "#paramsSize" "(" Params ")"   [function]
    syntax Int       ::= "#paramSize"  "(" Param  ")"   [function]
 // --------------------------------------------------------------
    rule #paramsSize(.Params) => 0

    rule #paramsSize(P PS)    => #paramSize(P) +Int #paramsSize(PS)

    rule #paramSize(%param(_, %bytes(_))) => 32

    rule #paramSize(%param(_, T)) => #size(T)    requires notBool isByteArrayType(T)


    syntax Int       ::= "#size" "(" Type ")"     [function]
 // -------------------------------------------------------
    rule #size(T:BaseType) => 32

    rule #size(%bytes(L)) => #ceil32(L) +Int 64

    rule #size(%list(T, L)) => #size(T) *Int L

    rule #size(%struct(.VarDecls)) => 0

    rule #size(%struct(%vdecl(_, T) VS)) => #size(T) +Int #size(%struct(VS))


    syntax Int       ::= "#ceil32" "(" Int ")"     [function]
 // ---------------------------------------------------------
    rule #ceil32(I) => I +Int 31 -Int (I -Int 1) %Int 32


    syntax Bool      ::= "#inDecorators" "(" Decorator "," Decorators ")"      [function]
 // -------------------------------------------------------------------------------------
    rule #inDecorators(D, .Decorators) => false

    rule #inDecorators(D, DEC DECS) => true                     requires D ==K DEC

    rule #inDecorators(D, DEC DECS) => #inDecorators(D, DECS)   requires D =/=K DEC


    syntax LLLExps  ::= "#mkClamper"        "(" Type "," Int /*data pos*/ "," Int /*mem pos*/ "," Bool ")"    [function]
    syntax LLLExps  ::= "#mkClamperForList" "(" Int /*length*/ "," Type "," Int "," Int "," Bool ")"          [function]
    syntax LLLExp   ::= "#mkCopier"         "(" LLLExp "," LLLExp "," LLLExp "," Bool ")"                     [function]
    syntax LLLExp   ::= "#mkDataDecl"       "(" LLLExp "," Bool ")"                                           [function]
 // --------------------------------------------------------------------------------------------------------------------
    rule #mkClamper(%num     , DPOS, MPOS, ISINIT) => $clamp(
                                                    $mload(#minNumPos),
                                                    #mkDataDecl(DPOS, ISINIT),
                                                    $mload(#maxNumPos)
                                                );.LLLExps

    rule #mkClamper(%bool    , DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), 2);.LLLExps

    rule #mkClamper(%address , DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), $mload(#addrSizePos));.LLLExps

    rule #mkClamper(%bytes(L), DPOS, MPOS, ISINIT)
             => $seq(
                    #mkCopier(MPOS, #mkDataDecl(DPOS, ISINIT), 32 +Int L, ISINIT);
                    $assert(
                        $le(
                            $calldataload($add(4, #mkDataDecl(DPOS, ISINIT))),
                            L
                        )
                    )
                );.LLLExps

    rule #mkClamper(%list(T, L), DPOS, MPOS, ISINIT) => $seq(#mkClamperForList(L, T, DPOS, MPOS, ISINIT));.LLLExps

    rule #mkClamperForList(0, T, DPOS, MPOS, ISINIT) => .LLLExps

    rule #mkClamperForList(L, T, DPOS, MPOS, ISINIT)
             => #extLLL(
                    #mkClamper(T, DPOS, MPOS, ISINIT),
                    #mkClamperForList(L -Int 1, T, DPOS +Int #size(T), MPOS +Int #size(T), ISINIT)
                )

    rule #mkCopier(MPOS, POS, SZ, true) => $codecopy(MPOS, $add(~codelen, POS), SZ)

    rule #mkCopier(MPOS, POS, SZ, false) => $calldatacopy(MPOS, $add(4, POS), SZ)

    rule #mkDataDecl(DATAPOS, true) => $codeload($add(~codelen, DATAPOS))

    rule #mkDataDecl(DATAPOS, false) => $calldataload($add(4, DATAPOS))




    syntax LLLExps  ::= "#initializer_lll"      [function]
 // ------------------------------------------------------
    rule #initializer_lll => $seq(
                                 $mstore(28 , $calldataload(0));
                                 $mstore(#addrSizePos , 2  ^Int 160);
                                 $mstore(#maxNumPos , 2  ^Int 127 -Int 1);
                                 $mstore(#minNumPos , -2 ^Int 127);
                                 $mstore(#maxDecimalPos, (2  ^Int 127 -Int 1) *Int 10000000000);
                                 $mstore(#minDecimalPos, (-2 ^Int 127) *Int 10000000000)
                             );.LLLExps


    syntax KItem     ::= "#env" "(" Map "," Int ")"
 // ----------------------------------------------
    rule <k> #env(ENV, I) => . ...</k>
         <env> _ => ENV </env>
         <nextMem> _ => I </nextMem>            [structural]
    rule (#env(_, _) => .) ~> #env(_, _)        [structural]


    syntax KItem    ::= "#exception" "(" String ")"
 // -----------------------------------------------

endmodule
