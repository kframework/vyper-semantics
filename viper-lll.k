require "viper-lll-interface.k"
require "viper-config.k"
require "utils.k"
require "domains.k"

module VIPER-LLL
    imports VIPER-LLL-INTERFACE
    imports VIPER-SYNTAX
    imports LLL-SYNTAX
    imports VIPER-CONFIG
    imports UTILS
    imports STRING
    imports KRYPTO

    // Convention: C'Sort' is an one-one corresponding supersort of Sort which
    //             requires for evaluation (i.e. not KResult).
    syntax CLLLExp  ::= LLLExp
    syntax CLLLExps ::= LLLExps
    syntax CType    ::= Type
    syntax CTypedAddr ::= TypedAddr


    syntax KResult  ::= LLLExp
                      | LLLExps
                      | TypedAddr
                      | Type
                      | Bool
                      | Int
   

    syntax KItem    ::= "#compileViperToLLL"    "(" Pgm ")"
    syntax KItem    ::= "#compileViperToLLLAux" "(" CLLLExps /*initializer*/ ","
                                                    CLLLExps /*init func*/   ","
                                                    CLLLExps /*regular func*/
                                                 ")"                 [seqstrict]
    syntax KItem    ::= "#compileViperToLLLAux" "(" CLLLExps /*initializer*/ ","
                                                    CLLLExps /*regular func*/
                                                ")"                  [seqstrict]
 // ----------------------------------------------------------------------------
    rule #compileViperToLLL(%pgm(GS, INIT, DEFS)) => #resolveGlobals(GS)
                                                  ~> #compileViperToLLLAux(
                                                         #initializer_lll,
                                                         #resolveFunc(INIT),
                                                         #resolveFuncs(DEFS))

    rule #compileViperToLLL(%pgm(GS, DEFS)) => #resolveGlobals(GS)
                                            ~> #compileViperToLLLAux(
                                                   #initializer_lll,
                                                   #resolveFuncs(DEFS))

    rule <k> #compileViperToLLLAux(INITIALIZER, INITFUNC, OTHERFUNCS) => . ... </k>
         <lll> _ => $%seq(
                      $%seq(INITIALIZER) ++LLL INITFUNC ++LLL
                      $return(
                        0,
                        $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0)))</lll>

    rule <k> #compileViperToLLLAux(INITIALIZER, OTHERFUNCS) => . ... </k>
         <lll> _ => $%seq(
                      $return(
                        0,
                        $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0));.LLLExps)</lll>


    syntax TypedAddr ::= "@taddr" "(" Type "," Int "," Bool /*global*/ "," Bool /*mutable*/ ")"
                       | "@notfound"
    syntax KItem     ::= "#resolveGlobals" "(" Globals ")"
 // -------------------------------------------------------------------------------------------
    rule #resolveGlobals(.Globals) => .

    rule <k> #resolveGlobals(%svdecl(NAME, T, _) GS) => #resolveGlobals(GS) ... </k>
         <global> GLOBAL => GLOBAL[%svar(NAME) <- @taddr(T, LOC, true, true)] </global>
         <nextStorage> LOC => LOC +Int 1 </nextStorage>


    syntax CLLLExps ::= "#append" "(" CLLLExps "," CLLLExps ")"       [seqstrict]
 // -----------------------------------------------------------------------------
    rule #append(C1:LLLExps, C2:LLLExps) => C1 ++LLL C2


    syntax CLLLExps ::= "#resolveFuncs"    "(" Defs ")"
    syntax CLLLExps ::= "#resolveFuncsAux" "(" Defs "," CLLLExps ")"  [strict(2)]
 // -----------------------------------------------------------------------------
    rule #resolveFuncs(DEFS) => #resolveFuncsAux(DEFS, .LLLExps)
    rule #resolveFuncsAux(.Defs, CODE) => CODE
    rule #resolveFuncsAux(DEF DEFS, CODE) => #resolveFuncsAux(DEFS, #append(CODE, #resolveFunc(DEF)))


    syntax CLLLExps ::= "#resolveFunc"    "(" Def  ")"
    syntax CLLLExps ::= "#resolveFuncAux" "(" CLLLExps /*copy input*/      ","
                                              CLLLExps /*check decorator*/ ","
                                              CLLLExps /*fill params*/     ","
                                              CLLLExps /*resolve stmts*/   ","
                                              Int      /*method id*/       ","
                                              Bool     /*is init?*/
                                          ")"                      [seqstrict]
 // --------------------------------------------------------------------------
    rule <k> #resolveFunc(%fdecl(DECS, NAME, PARAMS, T, STMTS))
                 => #resolveFuncAux(#copyInput(PARAMS, #isInitFunc(NAME)),
                                    #checkDecorators(DECS),
                                    #fillParams(PARAMS, 0, #isInitFunc(NAME)),
                                    #resolveStmts(STMTS),
                                    #generateMethodId(NAME, PARAMS),
                                    #isInitFunc(NAME))
                 ~> #env(ENV, LOC, ISCONSTANT, ISPAYABLE) ... </k>
         <env> ENV </env>
         <nextMem> LOC </nextMem>
         <constant> ISCONSTANT </constant>
         <payable> ISPAYABLE </payable>


    rule #resolveFuncAux(COPYINPUT, CHECKDECS, FILLPARAMS, STMTS, _, true)
             => $%seq(COPYINPUT ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL STMTS);.LLLExps

    rule #resolveFuncAux(COPYINPUT, CHECKDECS, FILLPARAMS, STMTS, METHODID, false)
             => $if(
                  $eq($mload(0), METHODID),
                  $%seq(COPYINPUT ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL STMTS ++LLL $stop));.LLLExps


    syntax CLLLExps ::= "#copyInput" "(" Params "," Bool /*is init?*/ ")"
 // -------------------------------------------------------------------------
    rule <k> #copyInput(PARAMS, true) => $codecopy(#reservedMemPos,
                                                   $codelen, 
                                                   #sizeOfParams(PARAMS));.LLLExps ... </k>
         <nextMem> M => M +Int #sizeOfParams(PARAMS) </nextMem>

    rule <k> #copyInput(PARAMS, false) => $calldatacopy(#reservedMemPos, 
                                                        4, 
                                                        #sizeOfParams(PARAMS));.LLLExps ... </k>
         <nextMem> M => M +Int #sizeOfParams(PARAMS) </nextMem>


    syntax CLLLExps ::= "#checkDecorators" "(" Decorators ")"
    syntax CLLLExps ::= "#checkConstant"   "(" Decorators ")"
    syntax CLLLExps ::= "#checkPayable"    "(" Decorators ")"
    syntax CLLLExps ::= "#checkInternal"   "(" Decorators ")"
 // -------------------------------------------------------------
    rule #checkDecorators(DECS) => #append(
                                       #checkConstant(DECS),
                                       #append(
                                           #checkPayable(DECS),
                                           #checkInternal(DECS)))

    rule <k> #checkConstant(DECS) => .LLLExps ... </k>
         <constant> _ => true </constant>
      requires #inDecorators(%@constant, DECS)

    rule <k> #checkConstant(DECS) => .LLLExps ... </k>
         <constant> _ => false </constant>
      requires notBool #inDecorators(%@constant, DECS)

    rule <k> #checkPayable(DECS) => .LLLExps ... </k>
         <payable> _ => true </payable>
      requires #inDecorators(%@payable, DECS)

    rule <k> #checkPayable(DECS) => $assert($iszero($callvalue));.LLLExps ... </k>
         <payable> _ => false </payable>
      requires notBool #inDecorators(%@payable, DECS)

    rule <k> #checkInternal(DECS) => $assert($eq($caller, $address));.LLLExps ... </k>
      requires #inDecorators(%@internal, DECS)

    rule #checkInternal(DECS) => .LLLExps
      requires notBool #inDecorators(%@internal, DECS)


    syntax CLLLExps ::= "#fillParam"  "(" Param  "," Int "," Bool ")"
    syntax CLLLExps ::= "#fillParams" "(" Params "," Int /*data pos*/ "," Bool")"
 // --------------------------------------------------------------------------------
    rule <k> #fillParam(%param(NAME, %bytes(L)), DATAPOS, ISINIT) => #mkClamper(%bytes(L), DATAPOS, LOC, ISINIT) ... </k>
         <env> ENV => #updateEnv(%var(NAME), %bytes(L), LOC, ENV, false)</env>
         <nextMem> LOC => LOC +Int #sizeOfType(%bytes(L)) </nextMem>

    rule <k> #fillParam(%param(NAME, T), DATAPOS, ISINIT) => #mkClamper(T, DATAPOS, LOC, ISINIT) ... </k>
         <env> ENV => #updateEnv(%var(NAME), T, #reservedMemPos +Int DATAPOS, ENV, false) </env>
         <nextMem> LOC </nextMem>
      requires notBool isByteArrayType(T)

    rule #fillParams(.Params, _, _) => .LLLExps

    rule #fillParams(P PS, DATAPOS, ISINIT)
             => #append(#fillParam(P, DATAPOS, ISINIT), #fillParams(PS, DATAPOS +Int #sizeOfParam(P), ISINIT))


    syntax CLLLExps ::= "#resolveStmts"    "(" Stmts ")"
    syntax CLLLExps ::= "#resolveStmtsAux" "(" Stmts "," CLLLExps ")"
 // -------------------------------------------------------------------------
    rule #resolveStmts(.Stmts) => .LLLExps

    rule #resolveStmts(STMT .Stmts) => #resolveStmt(STMT)

    rule #resolveStmts(STMTS) => #resolveStmtsAux(STMTS, .LLLExps)
      requires #sizeOfStmts(STMTS) >Int 1

    rule #resolveStmtsAux(.Stmts, CODE) => CODE

    rule #resolveStmtsAux(STMT STMTS, CODE) => #resolveStmtsAux(STMTS, #append(CODE, #resolveStmt(STMT)))


    syntax CLLLExps ::= "#resolveStmt"     "(" Stmt ")"
 // -------------------------------------------------------
    rule #resolveStmt(%assign(V, E)) => #assignHelper(V, #resolveExpr(E), #resolveExprType(E))
    rule #resolveStmt(%throw) => $assert(0);.LLLExps


    syntax CLLLExp ::= "#assignHelper" "(" Var                            ","
                                           CLLLExp  /*compiled Expr*/     ","
                                           CType    /*resovled ExprType*/
                                       ")"                   [seqstrict(2,3)]
 // -------------------------------------------------------------------------
    rule #assignHelper(V, CODE:LLLExp, T:Type) => #mkSetter(#lookupOrAllocVar(V, T), CODE, T)


    syntax CTypedAddr ::= "#lookupVar" "(" Var ")"
 // ----------------------------------------------
    rule <k> #lookupVar(%var(NAME)) => TADDR ... </k>
         <env> %var(NAME) |-> TADDR:TypedAddr ENV </env>

    rule <k> #lookupVar(%var(NAME)) => @notfound ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in keys(ENV)


    syntax KItem  ::= "#allocVar" "(" Var "," Type ")"
 // --------------------------------------------------
    rule <k> #allocVar(%var(NAME), T) => . ...</k>
         <env> ENV => #updateEnv(%var(NAME), T, LOC, ENV, true) </env>
         <nextMem> LOC => LOC +Int #sizeOfType(T) </nextMem>
      requires notBool %var(NAME) in keys(ENV)

    rule <k> #allocVar(%var(NAME), T)
                 => #exception("Duplicate variable name: " +String Id2String(NAME)) ...</k>
         <env> ENV </env>
      requires %var(NAME) in keys(ENV)


    syntax CTypedAddr ::= "#lookupOrAllocVar" "(" Var "," Type ")"
 // --------------------------------------------------------------
    rule <k> #lookupOrAllocVar(%var(NAME), _) => TADDR ... </k>
         <env> %var(NAME) |-> TADDR:TypedAddr ENV </env>

    rule <k> #lookupOrAllocVar(%var(NAME), T) => @taddr(T, LOC, false, true) ...</k>
         <env> ENV => #updateEnv(%var(NAME), T, LOC, ENV, true) </env>
         <nextMem> LOC => LOC +Int #sizeOfType(T) </nextMem>
      requires notBool %var(NAME) in keys(ENV)

    rule <k> #lookupOrAllocVar(%svar(NAME), _) => TADDR ... </k>
         <global> %svar(NAME) |-> TADDR:TypedAddr GLOBAL </global>

    rule <k> #lookupOrAllocVar(%svar(NAME), _)
                 => #exception("Persistent variable undeclared: " +String Id2String(NAME)) ... </k>
         <global> GLOBAL </global>
      requires notBool %svar(NAME) in keys(GLOBAL)


    syntax LLLExp  ::= "#mkSetter"    "(" CTypedAddr /*left variable address*/   ","
                                          LLLExp     /*right compiled Expr*/     ","
                                          Type       /*right resovled ExprType*/
                                      ")"                                [strict(1)]
    syntax LLLExp  ::= "#mkSetterAux" "(" TypedAddr "," LLLExp "," Type ")"
 // --------------------------------------------------------------------------------
    rule <k> #mkSetter(@taddr(_, _, true, _), _, _)
                 => #exception("Cannot modify storage inside a constant function!") ... </k>
         <constant> true </constant>

    rule <k> #mkSetter(@taddr(_, _, false, false), _, _)
                 => #exception("Cannot modify function argument") ...</k>

    rule <k> #mkSetter(@taddr(LEFTT, LOC, ISGLOBAL, true), CODE, RIGHTT)
                 => #mkSetterAux(@taddr(LEFTT, LOC, ISGLOBAL, true), CODE, RIGHTT) ... </k>
         <constant> ISCONSTANT </constant>
       requires ISGLOBAL =/=K ISCONSTANT



    syntax CLLLExp ::= "#resolveExpr" "(" Expr ")"
 // --------------------------------------------------
    rule #resolveExpr(%self) => $address

    rule <k> #resolveExpr(%var(NAME)) => $mload(LOC) ...</k>
         <env> %var(NAME) |-> @taddr(_, LOC, _, _) ENV </env>

    rule <k> #resolveExpr(%var(NAME)) => #exception("Undeclared Variable:" +String Id2String(NAME)) ...</k>
         <env> ENV </env>
      requires notBool %var(NAME) in keys(ENV)


    syntax CType   ::= "#resolveExprType" "(" Expr ")"
 // --------------------------------------------------
    rule #resolveExprType(%self) => %address

    rule <k> #resolveExprType(%var(NAME)) => T ...</k>
         <env> %var(NAME) |-> @taddr(T, _, _, _) ENV </env>
   

    syntax KItem       ::= "#env" "(" Map "," Int "," Bool "," Bool ")"
 // -----------------------------------------------------------------
    rule <k> CODE:LLLExps ~> (#env(ENV, LOC, ISCONSTANT, ISPAYABLE) => .) ...</k>
         <env> _ => ENV </env>
         <nextMem> _ => LOC </nextMem>
         <constant> _ => ISCONSTANT </constant>
         <payable> _ => ISPAYABLE </payable>                [structural]


    syntax KItem       ::= "#exception" "(" String ")"
 // --------------------------------------------------


//////////////////////////////////////////////////////////////////////////////
// Utils
//////////////////////////////////////////////////////////////////////////////


    syntax Bool ::= "#isInitFunc" "(" Id ")"    [function]
 // ------------------------------------------------------
    rule #isInitFunc(NAME) => NAME ==K __init__


    syntax Map  ::= "#updateEnv" "(" Var "," Type "," Int "," Map "," Bool /*mutable*/ ")"   [function]
    syntax Map  ::= "#flattenStruct" "(" Var "," VarDecls "," Int "," Map "," Bool ")"       [function]
 // ---------------------------------------------------------------------------------------------------
    rule #updateEnv(V, %struct(VARDECLS), LOC, M, ISMUTABLE) => #flattenStruct(V, VARDECLS, LOC, M, ISMUTABLE)

    rule #updateEnv(V, T, LOC, M, ISMUTABLE) => M[V <- @taddr(T, LOC, false, ISMUTABLE)]    requires notBool isStructType(T)

    rule #flattenStruct(V, .VarDecls, LOC, M, ISMUTABLE) => M

    rule #flattenStruct(V, %vdecl(NAME, T) VS, LOC, M, ISMUTABLE)
             => #flattenStruct(V, VS, LOC +Int #sizeOfType(T), #updateEnv(%mem(V, NAME), T, LOC, M, ISMUTABLE), ISMUTABLE)


    syntax Int       ::= "#sizeOfParams" "(" Params ")"   [function]
    syntax Int       ::= "#sizeOfParam"  "(" Param  ")"   [function]
 // --------------------------------------------------------------
    rule #sizeOfParams(.Params) => 0

    rule #sizeOfParams(P PS)    => #sizeOfParam(P) +Int #sizeOfParams(PS)

    rule #sizeOfParam(%param(_, %bytes(_))) => 32

    rule #sizeOfParam(%param(_, T)) => #sizeOfType(T)    requires notBool isByteArrayType(T)


    syntax Int       ::= "#sizeOfType" "(" Type ")"     [function]
 // --------------------------------------------------------------
    rule #sizeOfType(T:BaseType) => 32

    rule #sizeOfType(%bytes(L)) => #ceil32(L) +Int 64

    rule #sizeOfType(%list(T, N)) => #sizeOfType(T) *Int N

    rule #sizeOfType(%struct(.VarDecls)) => 0

    rule #sizeOfType(%struct(%vdecl(_, T) VS)) => #sizeOfType(T) +Int #sizeOfType(%struct(VS))


    syntax Int       ::= "#ceil32" "(" Int ")"     [function]
 // ---------------------------------------------------------
    rule #ceil32(I) => I +Int 31 -Int (I -Int 1) %Int 32


    syntax Bool      ::= "#inDecorators" "(" Decorator "," Decorators ")"      [function]
 // -------------------------------------------------------------------------------------
    rule #inDecorators(D, .Decorators) => false

    rule #inDecorators(D, DEC DECS) => true                     requires D ==K DEC

    rule #inDecorators(D, DEC DECS) => #inDecorators(D, DECS)   requires D =/=K DEC


    syntax String    ::= "#canonicalizeType" "(" Type ")"  [function]
 // -----------------------------------------------------------------
    rule #canonicalizeType(%bytes(L)) => "bytes"

    rule #canonicalizeType(%list(T, N)) => #canonicalizeType(T) +String "[" +String Int2String(N) +String "]"
         requires isBaseType(T)

    rule #canonicalizeType(%num) => "int128"

    rule #canonicalizeType(%decimal) => "decimal10"
   
    rule #canonicalizeType(%bool) => "bool"
 
    rule #canonicalizetype(%address) => "address"
 
    rule #canonicalizetype(%bytes32) => "bytes32"


    syntax String   ::= "#generateSignature" "(" String "," Params ")"  [function]
 // ------------------------------------------------------------------------------
    rule #generateSignature(SIGN, %param(_,T) PARAM1 PARAMS) 
             => #generateSignature(SIGN +String #canonicalizeType(T) +String "," , PARAM1 PARAMS)
    
    rule #generateSignature(SIGN, %param(_,T) .Params) 
             => #generateSignature(SIGN +String #canonicalizeType(T), .Params)

    rule #generateSignature(SIGN, .Params) => SIGN +String ")"


    syntax Int     ::= "#generateMethodId" "(" Id "," Params ")"       [function]
 // ------------------------------------------------------------------------------
    rule #generateMethodId(__init__, PARAMS) => 0

    rule #generateMethodId(NAME, PARAMS)
             => String2Base(substrString(Keccak256(#generateSignature(Id2String(NAME) +String "(", PARAMS)), 0, 8), 16)
      requires NAME =/=K __init__


    syntax LLLExps  ::= List{LLLExp, ";"}
    syntax LLLExp   ::= "$%seq" "(" LLLExps ")"
    syntax LLLExps  ::= LLLExps "++LLL" LLLExps      [left, function]
 // -----------------------------------------------------------------
    rule .LLLExps    ++LLL LES:LLLExps => LES
    rule (LE ; LES1) ++LLL LES2        => LE ; (LES1 ++LLL LES2)


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
             => $%seq(
                  #mkCopier(MPOS, #mkDataDecl(DPOS, ISINIT), 32 +Int L, ISINIT);
                  $assert(
                    $le(
                      $calldataload($add(4, #mkDataDecl(DPOS, ISINIT))),
                      L
                    )
                  )
                );.LLLExps

    rule #mkClamper(%list(T, N), DPOS, MPOS, ISINIT) => $%seq(#mkClamperForList(N, T, DPOS, MPOS, ISINIT));.LLLExps

    rule #mkClamperForList(0, T, DPOS, MPOS, ISINIT) => .LLLExps

    rule #mkClamperForList(N, T, DPOS, MPOS, ISINIT)
             => #mkClamper(T, DPOS, MPOS, ISINIT) ++LLL
                #mkClamperForList(N -Int 1, T, DPOS +Int #sizeOfType(T), MPOS +Int #sizeOfType(T), ISINIT)

    rule #mkCopier(MPOS, POS, SZ, true) => $codecopy(MPOS, $add($codelen, POS), SZ)

    rule #mkCopier(MPOS, POS, SZ, false) => $calldatacopy(MPOS, $add(4, POS), SZ)

    rule #mkDataDecl(DATAPOS, true) => $codeload($add($codelen, DATAPOS))

    rule #mkDataDecl(DATAPOS, false) => $calldataload($add(4, DATAPOS))


    syntax LLLExps  ::= "#initializer_lll"      [function]
 // ------------------------------------------------------
    rule #initializer_lll => $%seq(
                               $mstore(28 , $calldataload(0));
                               $mstore(#addrSizePos , 2  ^Int 160);
                               $mstore(#maxNumPos , 2  ^Int 127 -Int 1);
                               $mstore(#minNumPos , -2 ^Int 127);
                               $mstore(#maxDecimalPos, (2  ^Int 127 -Int 1) *Int 10000000000);
                               $mstore(#minDecimalPos, (-2 ^Int 127) *Int 10000000000)
                             );.LLLExps


    syntax Int      ::= "#sizeOfStmts" "(" Stmts ")"    [function]
 // --------------------------------------------------------------
    rule #sizeOfStmts(.Stmts) => 0
    rule #sizeOfStmts(STMT STMTS) => 1 +Int #sizeOfStmts(STMTS)


endmodule
