require "viper-lll-interface.k"
require "viper-config.k"
require "utils.k"

module VIPER-LLL
    imports VIPER-LLL-INTERFACE
    imports VIPER-SYNTAX
    imports LLL-SYNTAX
    imports VIPER-CONFIG
    imports UTILS
    imports STRING
    imports KRYPTO

    syntax CompileCode ::= LLLExps
                         | TypedAddr


    syntax KResult     ::= LLLExp
                         | LLLExps
                         | TypedAddr
                         | Bool
   

    syntax KItem     ::= "#compileViperToLLL"    "(" Pgm ")"
    syntax KItem     ::= "#compileViperToLLLAux" "(" CompileCode /*initializer*/ ","
                                                     CompileCode /*init func*/   "," 
                                                     CompileCode /*regular func*/
                                                 ")"                     [seqstrict]
    syntax KItem     ::= "#compileViperToLLLAux" "(" CompileCode /*initializer*/ ","
                                                     CompileCode /*regular func*/
                                                 ")"                     [seqstrict]
 // --------------------------------------------------------------------------------
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


    syntax TypedAddr ::= "@taddr" "(" Type "," Int "," Bool /*mutable*/ ")"
                       | "@taddr" "(" Map ")"    // struct
    syntax KItem     ::= "#resolveGlobals" "(" Globals ")"
 // ------------------------------------------------------
    rule #resolveGlobals(.Globals) => .

    rule <k> #resolveGlobals(%svdecl(NAME, T, _) GS) => #resolveGlobals(GS) ... </k>
         <global> GLOBAL => GLOBAL[%svar(NAME) <- @taddr(T, LOC, true)] </global>
         <nextStorage> LOC => LOC +Int 1 </nextStorage>


    syntax CompileCode ::= "#resolveFunc"    "(" Def  ")"
    syntax CompileCode ::= "#resolveFuncAux" "(" CompileCode /*copy input*/      ","
                                                 CompileCode /*check decorator*/ ","
                                                 CompileCode /*fill params*/     ","
                                                 CompileCode /*resolve stmts*/   ","
                                                 Int         /*method id*/       ","
                                                 Bool        /*is init?*/
                                             ")"                         [seqstrict]
 // --------------------------------------------------------------------------------
    rule #resolveFunc(%fdecl(DECS, NAME, PARAMS, T, STMTS))
             => #resolveFuncAux(#copyInput(PARAMS, #isInitFunc(NAME)),
                                #checkDecorators(DECS),
                                #fillParams(PARAMS, 0, #isInitFunc(NAME)),
                                #resolveStmts(STMTS),
                                #generateMethodId(NAME, PARAMS),
                                #isInitFunc(NAME))

    rule #resolveFuncAux(COPYINPUT, CHECKDECS, FILLPARAMS, STMTS, _, true)
             => $%seq(COPYINPUT ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL STMTS);.LLLExps

    rule #resolveFuncAux(COPYINPUT, CHECKDECS, FILLPARAMS, STMTS, METHODID, false)
             => $if(
                  $eq($mload(0), METHODID),
                  $%seq(COPYINPUT ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL STMTS ++LLL $stop));.LLLExps


    syntax CompileCode ::= "#append" "(" CompileCode "," CompileCode ")"  [seqstrict]
 // ---------------------------------------------------------------------------------
    rule #append(C1:LLLExps, C2:LLLExps) => C1 ++LLL C2


    syntax CompileCode ::= "#resolveFuncs"    "(" Defs ")"
    syntax CompileCode ::= "#resolveFuncsAux" "(" Defs "," CompileCode ")"  [strict(2)]
 // -----------------------------------------------------------------------------------
    rule #resolveFuncs(DEFS) => #resolveFuncsAux(DEFS, .LLLExps)
    rule #resolveFuncsAux(.Defs, CODE) => CODE
    rule #resolveFuncsAux(DEF DEFS, CODE) => #resolveFuncsAux(DEFS, #append(CODE, #resolveFunc(DEF)))


    syntax CompileCode ::= "#copyInput" "(" Params "," Bool /*is init?*/ ")"
 // ------------------------------------------------------------------------
    rule <k> #copyInput(PARAMS, true) => $codecopy(#reservedMemPos,
                                                   $codelen, 
                                                   #paramsSize(PARAMS));.LLLExps ... </k>
         <nextMem> M => M +Int #paramsSize(PARAMS) </nextMem>

    rule <k> #copyInput(PARAMS, false) => $calldatacopy(#reservedMemPos, 
                                                        4, 
                                                        #paramsSize(PARAMS));.LLLExps ... </k>
         <nextMem> M => M +Int #paramsSize(PARAMS) </nextMem>


    syntax CompileCode ::= "#checkDecorators" "(" Decorators ")"
    syntax CompileCode ::= "#checkConstant"   "(" Decorators ")"
    syntax CompileCode ::= "#checkPayable"    "(" Decorators ")"
    syntax CompileCode ::= "#checkInternal"   "(" Decorators ")"
 // ----------------------------------------------------------
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


    syntax CompileCode ::= "#fillParam"  "(" Param  "," Int "," Bool ")"
    syntax CompileCode ::= "#fillParams" "(" Params "," Int /*data pos*/ "," Bool")"
 // --------------------------------------------------------------------------------
    rule <k> #fillParam(%param(NAME, %bytes(L)), DATAPOS, ISINIT) => #mkClamper(%bytes(L), DATAPOS, M, ISINIT) ... </k>
         <env> ENV => #allocVar(%var(NAME), %bytes(L), M, ENV, false)</env>
         <nextMem> M => M +Int #size(%bytes(L)) </nextMem>

    rule <k> #fillParam(%param(NAME, T), DATAPOS, ISINIT) => #mkClamper(T, DATAPOS, M, ISINIT) ... </k>
         <env> ENV => #allocVar(%var(NAME), T, #reservedMemPos +Int DATAPOS, ENV, false) </env>
         <nextMem> M </nextMem>
      requires notBool isByteArrayType(T)

    rule #fillParams(.Params, _, _) => .LLLExps

    rule #fillParams(P PS, DATAPOS, ISINIT)
             => #append(#fillParam(P, DATAPOS, ISINIT), #fillParams(PS, DATAPOS +Int #paramSize(P), ISINIT))


    syntax CompileCode ::= "#resolveStmt"     "(" Stmt ")"
 // ------------------------------------------------------
    rule #resolveStmt(%throw) => $assert(0);.LLLExps


    syntax CompileCode ::= "#resolveStmts"    "(" Stmts ")"
    syntax CompileCode ::= "#resolveStmtsAux" "(" Stmts "," CompileCode ")"
 // ----------------------------------------------------------------------
    rule #resolveStmts(.Stmts) => .LLLExps

    rule #resolveStmts(STMT .Stmts) => #resolveStmt(STMT)

    rule #resolveStmts(STMTS) => #resolveStmtsAux(STMTS, .LLLExps)
      requires #sizeOfStmts(STMTS) >Int 1

    rule #resolveStmtsAux(.Stmts, CODE) => CODE

    rule #resolveStmtsAux(STMT STMTS, CODE) => #resolveStmtsAux(STMTS, #append(CODE, #resolveStmt(STMT)))


    syntax LLLExp    ::= "#mkSetter" "(" TypedAddr "," LLLExp ")"

    syntax TypedAddr ::= "#lookupVar(Var)"
 // --------------------------------------
   

    syntax KItem     ::= "#env" "(" Map "," Int ")"
 // ----------------------------------------------
    rule <k> #env(ENV, I) => . ...</k>
         <env> _ => ENV </env>
         <nextMem> _ => I </nextMem>            [structural]
    rule (#env(_, _) => .) ~> #env(_, _)        [structural]


    syntax KItem    ::= "#exception" "(" String ")"
 // -----------------------------------------------


//////////////////////////////////////////////////////////////////////////////
// Utils
//////////////////////////////////////////////////////////////////////////////


    syntax Bool ::= "#isInitFunc" "(" Id ")"    [function]
 // ------------------------------------------------------
    rule #isInitFunc(NAME) => NAME ==K __init__


    syntax Map  ::= "#allocVar" "(" Var "," Type "," Int "," Map "," Bool /*mutable*/ ")"    [function]
    syntax Map  ::= "#flattenStruct" "(" Var "," VarDecls "," Int "," Map "," Bool ")"       [function]
 // ---------------------------------------------------------------------------------------------------
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
 // --------------------------------------------------------
    rule #size(T:BaseType) => 32

    rule #size(%bytes(L)) => #ceil32(L) +Int 64

    rule #size(%list(T, N)) => #size(T) *Int N

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
             => #hex2Int(substrString(Keccak256(#generateSignature(Id2String(NAME) +String "(", PARAMS)), 0, 8))


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
                #mkClamperForList(N -Int 1, T, DPOS +Int #size(T), MPOS +Int #size(T), ISINIT)

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
