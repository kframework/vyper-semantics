/* Viper source code:
 * https://github.com/ethereum/viper/commit/67963b582d8a0c62fbef081df97e32f0ed5bb34d
 */

require "../common/viper-abstract-syntax.k"
require "../common/lll-abstract-syntax.k"
require "viper-lll-utils.k"
require "domains.k"

module VIPER-LLL
    imports VIPER-ABSTRACT-SYNTAX
    imports LLL-ABSTRACT-SYNTAX
    imports VIPER-LLL-UTILS
    imports STRING
    imports KRYPTO


///////////////////////////////////////////////////////////////////////////////
// Configuration / Context
///////////////////////////////////////////////////////////////////////////////


    configuration
    <T>
        <k> #compileViperToLLL($PGM:Pgm) </k>
        <lll> .K </lll>  // output lll program
        <env> .Map </env>  // In-memory variables. Var |-> TypedAddr
        <nextMem> @reservedMemPos </nextMem>  // Next available memory location
        <global> .Map </global>  // Global variables. Var |-> TypedAddr
        <nextStorage> 0 </nextStorage>
        <internalSig> .Map </internalSig>  // internal ABI objects.   (Event, Func)Name |-> (Event, Func)Record
        <externalSig> .Map </externalSig>  // external ABI objects.
        <forvar> .Set </forvar>  // Variables defined in for loops, eg. for i in range(6):...
        <return> %void </return>  // Return type of the function
        <constant> false </constant>  // Is the function constant?
        <payable> false </payable>  // Is the function payable?
        <placeholder> 1 </placeholder>  // Number of placeholders generated (used to generate random names)
    </T>


///////////////////////////////////////////////////////////////////////////////
// Data Types
///////////////////////////////////////////////////////////////////////////////


    syntax TypedAddr      ::= "@taddr" "(" Type ","
                                           LLLExp /*location*/   ","
                                           Bool   /*global?*/    ","
                                           Bool   /*mutable?*/   ")"

    syntax TypedLLLExp    ::= "@tlll"  "(" Type "," LLLExp ")"

    syntax EventRecord    ::= "@event" "(" Int /*event_id*/ "," EventParams ")"

    syntax FuncRecord     ::= "@func" "(" Int /*func_id*/    ","
                                          Params             ","
                                          Type               ","
                                          Bool /*constant?*/ ","
                                          Bool /*payable?*/  ","
                                          Bool /*internal?*/ ")"

    syntax PackedLoggingData  ::= "(" LLLExp    /*code*/ ","
                                      Int  /*start loc*/ ","
                                      Int       /*size*/ ")"

    syntax PackedArgBy32  ::= "(" LLLExps /*holder*/ ","
                                  Int      /*size*/  ")"

    // Convention: C'Sort' is a one-one corresponding supersort of Sort. C'Sort'
    //             requires for evaluation (i.e. not KResult).
    syntax CLLLExp                ::= LLLExp
    syntax CLLLExps               ::= LLLExps
    syntax CTypedLLLExp           ::= TypedLLLExp
    syntax CTypedAddr             ::= TypedAddr
    syntax CPackedLoggingData     ::= PackedLoggingData
    syntax CPackedArgBy32         ::= PackedArgBy32

    syntax KResult  ::= LLLExp
                      | LLLExps
                      | TypedLLLExp
                      | TypedAddr
                      | PackedLoggingData
                      | PackedArgBy32
                      | Bool
                      | Int


///////////////////////////////////////////////////////////////////////////////
// Preprocessing
///////////////////////////////////////////////////////////////////////////////


    syntax KItem  ::= "#compileViperToLLL"    "(" Pgm ")"
    syntax KItem  ::= "#compileViperToLLLAux" "(" CLLLExps /*header code*/  ","
                                                  CLLLExps /*init func*/    ","
                                                  CLLLExps /*regular func*/
                                               ")"                  [seqstrict]
    syntax KItem  ::= "#compileViperToLLLAux" "(" CLLLExps /*header code*/  ","
                                                  CLLLExps /*regular func*/
                                              ")"                   [seqstrict]
 // ---------------------------------------------------------------------------
    rule #compileViperToLLL(%pgm(ES, GS, INIT, DEFS)) => #addEvents(ES)
                                                      ~> #addGlobals(GS)
                                                      ~> #addFuncs((INIT .Defs) ++Def DEFS ++Def #mkPublicGetters(GS, .Defs))
                                                      ~> #compileViperToLLLAux(
                                                             #initializer_lll,
                                                             #compileFunc(INIT),
                                                             #compileFuncs(DEFS ++Def #mkPublicGetters(GS, .Defs), .LLLExps))

    rule #compileViperToLLL(%pgm(ES, GS, DEFS)) => #addEvents(ES)
                                                ~> #addGlobals(GS)
                                                ~> #addFuncs(DEFS ++Def #mkPublicGetters(GS, .Defs))
                                                ~> #compileViperToLLLAux(
                                                       #initializer_lll,
                                                       #compileFuncs(DEFS ++Def #mkPublicGetters(GS, .Defs), .LLLExps))

    rule <k> #compileViperToLLLAux(INITIALIZER, INITFUNC, OTHERFUNCS) => . ... </k>
         <lll> _ => $%seq(
                      ($%seq(INITIALIZER);.LLLExps) ++LLL INITFUNC ++LLL
                      ($return(
                         0,
                         $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0));.LLLExps)) </lll>

    rule <k> #compileViperToLLLAux(INITIALIZER, OTHERFUNCS) => . ... </k>
         <lll> _ => $%seq(
                      $return(
                        0,
                        $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0));.LLLExps) </lll>


// Process Events
// ==============


    syntax KItem  ::= "#addEvents"     "(" Events ")"
    syntax KItem  ::= "#addEvent"      "(" Event ")"
    syntax KItem  ::= "#addEventAux"   "(" Id "," EventParams ")"
 // -------------------------------------------------------------
    rule #addEvents(.Events) => .

    rule #addEvents(E ES) => #addEvent(E) ~> #addEvents(ES)

    rule #addEvent(%event(NAME, EPARAMS)) => #checkEventParams(EPARAMS, 0, .Ids)
                                          ~> #addEventAux(NAME, EPARAMS)

    rule <k> #addEventAux(NAME, EPARAMS) => . ... </k>
         <internalSig> SIGS
                      => SIGS[NAME <- @event(#computeEventId(NAME, EPARAMS), EPARAMS)] </internalSig>
      requires notBool NAME in keys(SIGS)

    rule <k> #addEventAux(NAME, EPARAMS) => #exception("Duplicate event name: " +String Id2String(NAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires NAME in keys(SIGS)


    syntax KItem  ::= "#checkEventParams"      "(" EventParams "," Int "," Ids ")"
    syntax KItem  ::= "#checkEventParamType"   "(" Type ")"
    syntax KItem  ::= "#checkNameDuplicateWithParams" "(" Id "," Ids ")"
 // ------------------------------------------------------------------------------
    rule #checkEventParams(.EventParams, TOPICNUM, NAMES) => .
      requires TOPICNUM <=Int 3

    rule #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
        => #checkEventParamType(T)
        ~> #checkNameDuplicateWithParams(NAME, NAMES)
        ~> #checkEventParams(EPARAMS, TOPICNUM +Int 1, NAMES ++Id NAME)
      requires TOPICNUM <Int 3

    rule #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
        => #exception("Maximum of 3 topics.")
      requires TOPICNUM >=Int 3

    rule #checkEventParams(%eparam(NAME, T, false) EPARAMS, TOPICNUM, NAMES)
        => #checkEventParamType(T)
        ~> #checkNameDuplicateWithParams(NAME, NAMES)
        ~> #checkEventParams(EPARAMS, TOPICNUM, NAMES ++Id NAME)

    rule #checkEventParamType(%bytesT(L)) => .
      requires L <=Int 32

    rule #checkEventParamType(%bytesT(L)) => #exception("Can only log a maximum of 32 bytes at a time.")
      requires L >Int 32

    rule #checkEventParamType(T) => .
      requires notBool isByteArrayType(T)

    rule #checkNameDuplicateWithParams(NAME, NAMES)
        => #exception("Duplicate function argument name: " +String Id2String(NAME))
      requires #inIds(NAME, NAMES)

    rule #checkNameDuplicateWithParams(NAME, NAMES) => .
      requires notBool #inIds(NAME, NAMES)


// Process Globals
// ===============


    syntax KItem  ::= "#addGlobals"   "(" Globals ")"
    syntax KItem  ::= "#addGlobal"    "(" Global  ")"
 // -------------------------------------------------
    rule #addGlobals(.Globals) => .

    rule #addGlobals(G GS) => #addGlobal(G) ~> #addGlobals(GS)

    rule <k> #addGlobal(%svdecl(NAME, T, _)) => . ... </k>
         <global> GLOBALS => GLOBALS[%svar(NAME) <- @taddr(T, LOC, true, true)] </global>
         <nextStorage> LOC => LOC +Int 1 </nextStorage>
      requires notBool NAME in keys(GLOBALS)

    rule <k> #addGlobal(%svdecl(NAME, T, _)) => #exception("Cannot declare a persistent variable twice!") ... </k>
         <global> GLOBALS </global>
      requires NAME in keys(GLOBALS)


// Process Funcs
// =============


    syntax KItem  ::= "#addFuncs"   "(" Defs ")"
    syntax KItem  ::= "#addFunc"    "(" Id   "," Params "," Type ","
                                        Bool /*constant?*/ ","
                                        Bool /*payable?*/  ","
                                        Bool /*internal?*/ ","
                                        Bool /*public?*/   ")"
    syntax KItem  ::= "#addFuncAux" "(" Id   "," Params "," Type ","
                                        Bool /*constant?*/ ","
                                        Bool /*payable?*/  ","
                                        Bool /*internal?*/ ")"
 // ------------------------------------------
    rule #addFuncs(.Defs) => .

    rule #addFuncs(%fdecl(DECS, NAME, PARAMS, T, STMTS) DEFS)
        => #addFunc(NAME, PARAMS, T,
                    #inDecorators(%@constant, DECS),
                    #inDecorators(%@payable, DECS),
                    #inDecorators(%@internal, DECS),
                    #inDecorators(%@public, DECS))
        ~> #addFuncs(DEFS)

    rule #addFunc(NAME, PARAMS, T, CONSTANT, PAYABLE, INTERNAL, PUBLIC)
        => #checkFuncParams(PARAMS, .Ids)
        ~> #checkInternalPublicMECE(INTERNAL, PUBLIC)
        ~> #addFuncAux(NAME, PARAMS, T, CONSTANT, PAYABLE, INTERNAL)

    rule <k> #addFuncAux(NAME, PARAMS, T, CONSTANT, PAYABLE, INTERNAL) => . ... </k>
         <internalSig> SIGS
                      => SIGS[NAME <- @func(#computeFuncId(NAME, PARAMS),
                                            PARAMS,
                                            T,
                                            CONSTANT,
                                            PAYABLE,
                                            INTERNAL)] </internalSig>
      requires notBool NAME in keys(SIGS)

    rule <k> #addFuncAux(NAME, _, _, _, _, _)
        => #exception("Duplicate event or function name: " +String Id2String(NAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires NAME in keys(SIGS)


    syntax KItem  ::= "#checkFuncParams"       "(" Params "," Ids ")"
    syntax KItem  ::= "#checkNameDuplicateWithGlobals" "(" Id ")"
 // -----------------------------------------------------------------
    rule #checkFuncParams(.Params, NAMES) => .

    rule #checkFuncParams(%param(NAME, _) PARAMS, NAMES)
        => #checkNameDuplicateWithParams(NAME, NAMES)
        ~> #checkNameDuplicateWithGlobals(NAME)

    rule <k> #checkNameDuplicateWithGlobals(NAME) => . ... </k>
         <global> GLOBALS </global>
      requires notBool %svar(NAME) in keys(GLOBALS)

    rule <k> #checkNameDuplicateWithGlobals(NAME)
            => #exception("Variable name duplicated between function arguments and globals: +String Id2String(NAME)")
         ... </k>
         <global> GLOBALS </global>
      requires %svar(NAME) in keys(GLOBALS)


    syntax KItem  ::= "#checkInternalPublicMECE" "(" Bool /*internal?*/ "," Bool /*public?*/ ")"
 // --------------------------------------------------------------------------------------------
    rule #checkInternalPublicMECE(INTERNAL, PUBLIC)
        => #ifThen(INTERNAL ==K true andBool PUBLIC ==K true,
                   #exception("Cannot use public and internal decorators on the same function."))
        ~> #ifThen(INTERNAL ==K false andBool PUBLIC ==K false,
                   #exception("Function visibility must be declared."))


    syntax Defs  ::= "#mkPublicGetters"         "(" Globals "," Defs ")"            [function]
    syntax Defs  ::= "#mkPublicGetter"          "(" String /*func name*/       ","
                                                    Params                     ","
                                                    Type                       ","
                                                    Var                        ","
                                                    Int     /*depth*/          ")"  [function]
    syntax Defs  ::= "#mkPublicGetterBase"      "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterByteArray" "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterListT"     "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterMapT"      "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterStructT"   "(" String "," Params "," Type "," Var "," Int ")"  [function]
 // -------------------------------------------------------------------------------------------------------------
    rule #mkPublicGetters(.Globals, DEFS) => DEFS

    rule #mkPublicGetters(%svdecl(NAME, T, %public) GS, DEFS)
        => #mkPublicGetters(GS,
                            DEFS ++Def #mkPublicGetter(Id2String(NAME), .Params, T, %svar(NAME), 0))

    rule #mkPublicGetters(%svdecl(_, _, %private) GS, DEFS)
           => #mkPublicGetters(GS, DEFS)

    rule #mkPublicGetter(NAME, PARAMS, T, VAR, DEPTH) => #mkPublicGetterBase(NAME, PARAMS, T, VAR, DEPTH)
      requires isBaseType(T)

    rule #mkPublicGetter(NAME, PARAMS, %bytesT(L), VAR, DEPTH)
        => #mkPublicGetterByteArray(NAME, PARAMS, %bytesT(L), VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, %listT(T, L), VAR, DEPTH)
        => #mkPublicGetterListT(NAME, PARAMS, %listT(T, L), VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, %mapT(VT, KT), VAR, DEPTH)
        => #mkPublicGetterMapT(NAME, PARAMS, %mapT(VT, KT), VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, %structT(VDECLS), VAR, DEPTH)
        => #mkPublicGetterStructT(NAME, PARAMS, %structT(VDECLS), VAR, DEPTH)

    rule #mkPublicGetterBase(NAME, PARAMS, T, VAR, DEPTH)
        => %fdecl(%@public %@constant .Decorators,
                  String2Id("get_" +String NAME),
                  PARAMS,
                  T,
                  %return(VAR) .Stmts) .Defs

    rule #mkPublicGetterByteArray(NAME, PARAMS, %bytesT(L), VAR, DEPTH)
        => %fdecl(%@public %@constant .Decorators,
                  String2Id("get_" +String NAME),
                  PARAMS,
                  %bytesT(L),
                  %return(VAR) .Stmts) .Defs

    rule #mkPublicGetterListT(NAME, PARAMS, %listT(T, L), VAR, DEPTH)
        => #mkPublicGetter(NAME,
                           PARAMS ++Param (%param(String2Id("arg" +String Int2String(DEPTH)), %num) .Params),
                           T,
                           %listelem(VAR, %var(String2Id("arg" +String Int2String(DEPTH)))),
                           DEPTH +Int 1)

    rule #mkPublicGetterMapT(NAME, PARAMS, %mapT(VT, KT), VAR, DEPTH)
        => #mkPublicGetter(NAME,
                           PARAMS ++Param (%param(String2Id("arg" +String Int2String(DEPTH)), KT) .Params),
                           VT,
                           %mapelem(VAR, %var(String2Id("arg" +String Int2String(DEPTH)))),
                           DEPTH +Int 1)

    rule #mkPublicGetterStructT(NAME, PARAMS, %structT(%vdecl(VNAME, T) VS), VAR, DEPTH)
        => #mkPublicGetter(NAME +String "___" +String Id2String(VNAME),
                           PARAMS,
                           T,
                           %mem(VAR, VNAME),
                           DEPTH)
           ++Def #mkPublicGetterStructT(NAME, PARAMS, %structT(VS), VAR, DEPTH)

    rule #mkPublicGetterStructT(NAME, PARAMS, %structT(.VarDecls), VAR, DEPTH)
        => .Defs


///////////////////////////////////////////////////////////////////////////////
// Header Code
///////////////////////////////////////////////////////////////////////////////


    syntax LLLExps  ::= "#initializer_lll"      [function]
 // ------------------------------------------------------
    rule #initializer_lll => $%seq(
                               $mstore(28 , $calldataload(0));
                               $mstore(@addrSizePos , 2 ^Int 160);
                               $mstore(@maxNumPos , 2 ^Int 127 -Int 1);
                               $mstore(@minNumPos , -2 ^Int 127);
                               $mstore(@maxDecimalPos, (2 ^Int 127 -Int 1) *Int 10000000000);
                               $mstore(@minDecimalPos, (-2 ^Int 127) *Int 10000000000)
                             );.LLLExps


///////////////////////////////////////////////////////////////////////////////
// Function Definitions
///////////////////////////////////////////////////////////////////////////////


    syntax CLLLExps ::= "#extendLLL" "(" CLLLExps "," CLLLExps ")"       [seqstrict]
 // --------------------------------------------------------------------------------
    rule #extendLLL(C1:LLLExps, C2:LLLExps) => C1 ++LLL C2


    syntax CLLLExps ::= "#compileFuncs" "(" Defs "," LLLExps ")"
 // ------------------------------------------------------------
    rule #compileFuncs(.Defs, RESULTCODE) => RESULTCODE

    rule #compileFuncs(DEF DEFS, RESULTCODE) => #compileFunc(DEF) ~> #compileFuncs(DEFS, RESULTCODE)

    rule (FUNCCODE:LLLExps ~> #compileFuncs(DEFS, RESULTCODE))
        => #compileFuncs(DEFS, RESULTCODE ++LLL FUNCCODE)


    syntax CLLLExps ::= "#compileFunc"    "(" Def  ")"
    syntax CLLLExps ::= "#compileFuncAux" "(" CLLLExps /*copy input*/      ","
                                              CLLLExps /*check decorator*/ ","
                                              CLLLExps /*fill params*/     ","
                                              CLLLExps /*resolve stmts*/   ","
                                              Int      /*func id*/         ","
                                              Bool     /*init?*/
                                          ")"                      [seqstrict]
 // --------------------------------------------------------------------------
    rule <k> #compileFunc(%fdecl(DECS, NAME, PARAMS, T, STMTS))
            => #compileFuncAux(#copyArg(PARAMS, #isInitFunc(NAME)),
                               #addClampersForDecorators(PAYABLE, INTERNAL),
                               #fillParams(PARAMS, 0, #isInitFunc(NAME), .LLLExps),
                               #compileStmts(STMTS, .LLLExps),
                               FUNCID,
                               #isInitFunc(NAME))
           ~> #cleanConfig ... </k>
         <internalSig> NAME |-> @func(FUNCID, _, T, CONSTANT, PAYABLE, INTERNAL) SIGS</internalSig>
         <return> _ => T </return>
         <constant> _ => CONSTANT </constant>
         <payable> _ => PAYABLE </payable>


    rule #compileFuncAux(COPYARG, CHECKDECS, FILLPARAMS, STMTS, _, true)
        => $%seq(COPYARG ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL ($%seq(STMTS);.LLLExps));.LLLExps

    rule #compileFuncAux(COPYARG, CHECKDECS, FILLPARAMS, STMTS, FUNCID, false)
        => $if(
             $eq($mload(0), FUNCID),
             $%seq(COPYARG ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL STMTS ++LLL ($stop;.LLLExps)));.LLLExps


// Copy Arguments
// ==============


    syntax CLLLExps ::= "#copyArg" "(" Params "," Bool /*init?*/ ")"
 // ----------------------------------------------------------------
    rule #copyArg(.Params, _) => $pass;.LLLExps

    rule <k> #copyArg(PARAMS, true) => $codecopy(@reservedMemPos,
                                                 $codelen,
                                                 #sizeOfParams(PARAMS));.LLLExps ... </k>
         <nextMem> M => M +Int #sizeOfParams(PARAMS) </nextMem>
      requires #sizeOfParams(PARAMS) >Int 0

    rule <k> #copyArg(PARAMS, false) => $calldatacopy(@reservedMemPos,
                                                      4,
                                                      #sizeOfParams(PARAMS));.LLLExps ... </k>
         <nextMem> M => M +Int #sizeOfParams(PARAMS) </nextMem>
      requires #sizeOfParams(PARAMS) >Int 0


// Add Clampers For Decorators
// ===========================


    syntax CLLLExps ::= "#addClampersForDecorators" "(" Bool "," Bool ")"
    syntax LLLExps  ::= "#checkPayable"    "(" Bool ")"    [function]
    syntax LLLExps  ::= "#checkInternal"   "(" Bool ")"    [function]
 // -----------------------------------------------------------------
    rule #addClampersForDecorators(PAYABLE, INTERNAL) => #checkPayable(PAYABLE) ++LLL #checkInternal(INTERNAL)

    rule #checkPayable(true) => .LLLExps

    rule #checkPayable(false) => $assert($iszero($callvalue));.LLLExps

    rule #checkInternal(true) => $assert($eq($caller, $address));.LLLExps

    rule #checkInternal(false) => .LLLExps


// Fill Parameters
// ===============


    syntax CLLLExps ::= "#fillParams" "(" Params "," Int /*data pos*/ "," Bool /*init?*/ "," LLLExps ")"
 // ----------------------------------------------------------------------------------------------------
    rule #fillParams(.Params, _, _, RESULTCODE) => RESULTCODE

    rule #fillParams(P PS, DATAPOS, ISINIT, RESULTCODE)
        => #fillParam(P, DATAPOS, ISINIT) ~> #fillParams(PS, DATAPOS +Int #sizeOfParam(P), ISINIT, RESULTCODE)

    rule (FILLCODE:LLLExps ~> #fillParams(PS, DATAPOS, ISINIT, RESULTCODE))
        => #fillParams(PS, DATAPOS, ISINIT, RESULTCODE ++LLL FILLCODE)


    syntax CLLLExps ::= "#fillParam"  "(" Param  "," Int "," Bool ")"
 // -----------------------------------------------------------------
    rule <k> #fillParam(%param(NAME, %bytesT(L)), DATAPOS, ISINIT) => #mkClamper(%bytesT(L), DATAPOS, LOC, ISINIT) ... </k>
         <env> ENV => #updateEnv(ENV, %var(NAME), %bytesT(L), LOC, false) </env>
         <nextMem> LOC => LOC +Int #sizeOfType(%bytesT(L)) </nextMem>

    rule <k> #fillParam(%param(NAME, T), DATAPOS, ISINIT) => #mkClamper(T, DATAPOS, LOC, ISINIT) ... </k>
         <env> ENV => #updateEnv(ENV, %var(NAME), T, @reservedMemPos +Int DATAPOS, false) </env>
         <nextMem> LOC </nextMem>
      requires notBool isByteArrayType(T)


    syntax LLLExps  ::= "#mkClamper"      "(" Type ","
                                              Int /*data pos*/ ","
                                              Int /*mem pos*/  ","
                                              Bool /*init?*/   ")"                                  [function]
    syntax LLLExps  ::= "#mkClamperListT" "(" Int /*length*/ "," Type "," Int "," Int "," Bool ")"  [function]
    syntax LLLExp   ::= "#mkCopier"       "(" LLLExp "," LLLExp "," LLLExp "," Bool ")"             [function]
    syntax LLLExp   ::= "#mkDataDecl"     "(" LLLExp "," Bool ")"                                   [function]
 // ------------------------------------------------------------------------------------------------------------
    rule #mkClamper(%num, DPOS, MPOS, ISINIT) => $clamp(
                                                   $mload(@minNumPos),
                                                   #mkDataDecl(DPOS, ISINIT),
                                                   $mload(@maxNumPos)
                                                 );.LLLExps

    rule #mkClamper(%unitT(%num, _, _), DPOS, MPOS, ISINIT) => $clamp(
                                                                 $mload(@minNumPos),
                                                                 #mkDataDecl(DPOS, ISINIT),
                                                                 $mload(@maxNumPos)
                                                               );.LLLExps

    rule #mkClamper(%bool, DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), 2);.LLLExps

    rule #mkClamper(%address, DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), $mload(@addrSizePos));.LLLExps

    // TODO: figure out what do these checks mean?
    rule #mkClamper(%bytesT(L), DPOS, MPOS, ISINIT)
        => $%seq(
             #mkCopier(MPOS, #mkDataDecl(DPOS, ISINIT), 32 +Int L, ISINIT);
             $assert(
               $le(
                 $calldataload($add(4, #mkDataDecl(DPOS, ISINIT))),
                 L
                )
             )
           );.LLLExps

    rule #mkClamper(%listT(T, N), DPOS, MPOS, ISINIT) => $%seq(#mkClamperListT(N, T, DPOS, MPOS, ISINIT));.LLLExps

    rule #mkClamperListT(1, T, DPOS, MPOS, ISINIT) => #mkClamper(T, DPOS, MPOS, ISINIT)

    rule #mkClamperListT(N, T, DPOS, MPOS, ISINIT)
             => #mkClamper(T, DPOS, MPOS, ISINIT) ++LLL
                #mkClamperListT(N -Int 1, T, DPOS +Int #sizeOfType(T), MPOS +Int #sizeOfType(T), ISINIT)
      requires N >Int 1

    rule #mkClamper(%decimal, _, _, _) => $pass;.LLLExps

    rule #mkClamper(%unitT(%decimal, _, _), _, _, _) => $pass;.LLLExps

    rule #mkClamper(%num256, _, _, _) => $pass;.LLLExps

    rule #mkClamper(%bytes32, _, _, _) => $pass;.LLLExps

    rule #mkClamper(%mapT(_, _), _, _, _) => $pass;.LLLExps

    rule #mkClamper(%structT(_), _, _, _) => $pass;.LLLExps

    rule #mkCopier(MPOS, POS, SIZE, true) => $codecopy(MPOS, $add($codelen, POS), SIZE)

    rule #mkCopier(MPOS, POS, SIZE, false) => $calldatacopy(MPOS, $add(4, POS), SIZE)

    rule #mkDataDecl(DATAPOS, true) => $codeload($add($codelen, DATAPOS))

    rule #mkDataDecl(DATAPOS, false) => $calldataload($add(4, DATAPOS))


///////////////////////////////////////////////////////////////////////////////
// Stmts
///////////////////////////////////////////////////////////////////////////////


    syntax CLLLExps ::= "#compileStmts" "(" Stmts "," LLLExps ")"
 // ----------------------------------------------------------------
    rule #compileStmts(.Stmts, RESULTCODE) => RESULTCODE

    rule #compileStmts(STMT STMTS, RESULTCODE) => #compileStmt(STMT) ~> #compileStmts(STMTS, RESULTCODE)

    rule (STMTCODE:LLLExps ~> #compileStmts(STMTS, RESULTCODE))
        => #compileStmts(STMTS, RESULTCODE ++LLL STMTCODE)


    syntax CLLLExps ::= "#compileStmt" "(" Stmt ")"
 // -------------------------------------------------------
    rule #compileStmt(%break) => $break; .LLLExps

    rule #compileStmt(%pass) => $pass;.LLLExps

    rule #compileStmt(%throw) => $assert(0);.LLLExps


// Annotated Assignment
// ====================


   rule #compileStmt(%vdecl(NAME, T)) => #newVar(NAME, T) ~> $pass;.LLLExps

   rule (@taddr(T, LOC, GLOBAL, MUTABLE) => .) ~> $pass;.LLLExps


// Assignment
// ==========


    rule #compileStmt(%assign(V, E)) => #assign(V, #resolveExpr(E))


    syntax CLLLExps ::= "#assign"    "(" Var                             ","
                                         CTypedLLLExp  /*compiled Expr*/
                                     ")"                         [strict(2)]
    syntax CLLLExps ::= "#assignAux" "(" CTypedAddr /*variable address*/ ","
                                         TypedLLLExp
                                     ")"                         [strict(1)]
 // ------------------------------------------------------------------------
    rule #assign(V, @tlll(T, CODE)) => #assignAux(#lookupOrNewVar(V, T), @tlll(T, CODE))

    rule <k> #assignAux(@taddr(LT, LOC, ISGLOBAL, ISMUTABLE), RTCODE)
            => #ifThen(ISGLOBAL ==K true andBool ISCONSTANT ==K true,
                       #exception("Cannot modify storage inside a constant function!"))
            ~> #ifThen(ISMUTABLE ==K false,
                       #exception("Cannot modify function argument"))
            ~> #mkSetter(@taddr(LT, LOC, ISGLOBAL, ISMUTABLE), RTCODE)
         ... </k>
         <constant> ISCONSTANT </constant>


    syntax CLLLExps ::= "#mkSetter"     "(" TypedAddr    /*left variable address*/   ","
                                            TypedLLLExp  /*right compiled Expr*/
                                        ")"
    syntax CLLLExps ::= "#mkSetterBase" "(" TypedAddr "," CTypedLLLExp ")"    [strict(2)]
 // -------------------------------------------------------------------------------------
    rule #mkSetter(@taddr(LT, LOC, ISGLOBAL, ISMUTABLE), RTCODE)
             => #mkSetterBase(@taddr(LT, LOC, ISGLOBAL, ISMUTABLE),
                              #baseTypeConvert(RTCODE, LT))
      requires isBaseType(LT)

    rule #mkSetterBase(@taddr(_, LOC, true, _), @tlll(_, CODE)) => $sstore(LOC, CODE);.LLLExps

    rule #mkSetterBase(@taddr(_, LOC, false, _), @tlll(_, CODE)) => $mstore(LOC, CODE);.LLLExps


    // Augassign
    syntax CLLLExps ::= "#augassign"    "(" AugAssignOp                     ","
                                            CTypedAddr /*variable address*/ ","
                                            CTypedLLLExp  /*compiled Expr*/
                                        ")"                    [seqstrict(2,3)]
    syntax CLLLExps ::= "#augassignAux" "(" TypedAddr /*variable address*/  ","
                                            CTypedLLLExp  /*compiled Expr*/
                                        ")"                         [strict(2)]
 // ---------------------------------------------------------------------------
    rule #compileStmt(%augassign(OP, V, E)) => #augassign(OP, #lookupVar(V), #resolveExpr(E))

    rule <k> #augassign(OP, @taddr(LT, LOC, true, _), RTCODE)
                 => #exception("Cannot modify storage inside a constant function!") ... </k>
         <constant> true </constant>

    rule <k> #augassign(OP, @taddr(LT, LOC, true, ISMUTABLE), RTCODE)
                 => #augassignAux(@taddr(LT, LOC, true, ISMUTABLE),
                                  #baseTypeConvert(
                                      #convertToBinaryArith(OP, @tlll(LT, $sload($stloc)), RTCODE),
                                      LT)) ... </k>
         <constant> false </constant>

    rule <k> #augassign(OP, @taddr(LT, LOC, false, ISMUTABLE), RTCODE)
                 => #augassignAux(@taddr(LT, LOC, false, ISMUTABLE),
                                  #baseTypeConvert(
                                      #convertToBinaryArith(OP, @tlll(LT, $mload($mloc)), RTCODE),
                                      LT)) ... </k>
          <constant> false </constant>

    rule #augassignAux(@taddr(_, LOC, true, _), @tlll(_, CODE))
             => $with($stloc, LOC, $sstore($stloc, CODE));.LLLExps

    rule #augassignAux(@taddr(_, LOC, false, _), @tlll(_, CODE))
             => $with($mloc, LOC, $mstore($mloc, CODE));.LLLExps


    syntax CTypedLLLExp ::= "#convertToBinaryArith" "(" AugAssignOp           ","
                                                        TypedLLLExp  /*left*/ ","
                                                        TypedLLLExp  /*right*/
                                                    ")"
 // ------------------------------------------------------------------------------
    rule #convertToBinaryArith(+=, LEXP, REXP) => #binOp(+, LEXP, REXP)

    rule #convertToBinaryArith(-=, LEXP, REXP) => #binOp(-, LEXP, REXP)

    rule #convertToBinaryArith(*=, LEXP, REXP) => #binOp(*, LEXP, REXP)

    rule #convertToBinaryArith(/=, LEXP, REXP) => #binOp(/, LEXP, REXP)


    // if
    syntax CLLLExps ::= "#if" "(" CTypedLLLExp /*TEST*/ ","
                                  CLLLExps     /*Then*/ ","
                                  CLLLExps     /*Else*/
                              ")"               [seqstrict]
    syntax CLLLExps ::= "#if" "(" CTypedLLLExp /*TEST*/ ","
                                  CLLLExps     /*Then*/
                              ")"               [seqstrict]
 // -------------------------------------------------------
    rule #compileStmt(%if(TEST, THENSTMTS, ELSESTMTS)) => #if(#resolveExpr(TEST),
                                                              #compileStmts(THENSTMTS, .LLLExps),
                                                              #compileStmts(ELSESTMTS, .LLLExps))

    rule #compileStmt(%if(TEST, THENSTMTS)) => #if(#resolveExpr(TEST), #compileStmts(THENSTMTS, .LLLExps))

    rule #if(@tlll(_, CODE), THEN:LLLExps, ELSE:LLLExps) => $if(CODE, $%seq(THEN), $%seq(ELSE));.LLLExps

    rule #if(@tlll(_, CODE), THEN:LLLExp) => $if(CODE, $%seq(THEN));.LLLExps


    // for
    syntax CLLLExps ::= "#for" "(" CTypedAddr             ","
                                   CTypedLLLExp /*start*/ ","
                                   Int         /*rounds*/ ","
                                   CLLLExps
                               ")"         [seqstrict(1,2,4)]
 // ---------------------------------------------------------
    // e.g. for i in range(10): ...
    rule #compileStmt(%for(NAME, ROUNDS, STMTS)) => #for(#newLoopVar(NAME), @tlll(%num, 0), ROUNDS, #compileStmts(STMTS, .LLLExps))

    // e.g. for i in range(100, 110): ...
    rule #compileStmt(%for(NAME, START:Int, END:Int, STMTS))
             => #for(#newLoopVar(NAME), @tlll(%num, START), END -Int START, #compileStmts(STMTS, .LLLExps))

    // e.g. for i in range(x, x + 10): ...
    rule #compileStmt(%for(NAME, %var(V), %binop(+, %var(V), ROUNDS:Int), STMTS))
             => #for(#newLoopVar(NAME), #resolveExpr(%var(V)), ROUNDS, #compileStmts(STMTS, .LLLExps))

    rule #for(@taddr(%num, LOC:Int, _, _), @tlll(_, STARTCODE), ROUNDS, BODYCODE:LLLExps)
             => $repeat(LOC, STARTCODE, ROUNDS, $%seq(BODYCODE));.LLLExps


    // return
    syntax CLLLExps ::= "#return" "(" CTypedLLLExp "," Type /*return type*/ ")"  [strict(1)]
    syntax CLLLExps ::= "#returnBase" "(" TypedLLLExp "," Type ")"
 // ----------------------------------------------------------------------------------------
    rule <k> #compileStmt(%return) => #ifThenElse(T =/=K %void,
                                                  #exception("Expecting to return a value"),
                                                  .LLLExps) ... </k>
         <return> T </return>

    rule <k> #compileStmt(%return(E)) => #ifThenElse(T =/=K %void,
                                                     #return(#resolveExpr(E), T),
                                                     #exception("Not expecting to return a value")) ... </k>
         <return> T </return>

    rule #return(@tlll(T, CODE), RETURNTYPE) => #returnBase(@tlll(T, CODE), RETURNTYPE)
      requires isBaseType(T)

    rule #returnBase(@tlll(T, CODE), RETURNTYPE)
             => #ifThenElse(T ==K RETURNTYPE,
                            $%seq($mstore(0, CODE); $return(0, 32);.LLLExps);.LLLExps,
                            #exception("Unsupported type conversion."))


    // send
    syntax CLLLExps ::= "#send" "(" CTypedLLLExp /*to*/ "," CTypedLLLExp /*value*/ ")"  [seqstrict]
 // -----------------------------------------------------------------------------------------------
    rule <k> #compileStmt(%send(TO, VALUE))
                 => #ifThenElse(CONSTANT ==K false,
                                #send(#resolveExpr(TO), #resolveExpr(VALUE)),
                                #exception("Cannot send ether inside a constant function")) ... </k>
         <constant> CONSTANT </constant>

    rule #send(@tlll(%address, TOCODE), @tlll(%unitT(%num, %wei, _), VALUECODE))
             => $assert($call(0, TOCODE, VALUECODE, 0, 0, 0, 0)); .LLLExps


    // log
    syntax CLLLExps ::= "#log"    "(" Exprs "," EventRecord ")"
    syntax CLLLExps ::= "#logAux" "(" Int /*event id*/  ","
                                      Exprs             ","
                                      EventParams       ","
                                      Exprs /*topic*/   ","
                                      EventParams       ","
                                      Exprs /*data*/    ","
                                      EventParams       ")"
    syntax CLLLExps ::= "#log1"  "(" CPackedLoggingData ","
                                     Int                ")"          [strict(1)]
    syntax CLLLExps ::= "#log2"  "(" CPackedLoggingData ","
                                     Int                ","
                                     CTypedLLLExp       ")"     [seqstrict(1,3)]
    syntax CLLLExps ::= "#log3"  "(" CPackedLoggingData ","
                                     Int                ","
                                     CTypedLLLExp       ","
                                     CTypedLLLExp       ")"   [seqstrict(1,3,4)]
    syntax CLLLExps ::= "#log4"  "(" CPackedLoggingData ","
                                     Int                ","
                                     CTypedLLLExp       ","
                                     CTypedLLLExp       ","
                                     CTypedLLLExp       ")" [seqstrict(1,3,4,5)]
 // --------------------------------------------------------------------------------
    rule <k> #compileStmt(%log(NAME, ARGS)) => #log(ARGS, EVENTRECORD) ... </k>
         <internalSig> NAME |-> EVENTRECORD SIGS </internalSig>

    rule <k> #compileStmt(%log(NAME, _)) => #exception("Event not declared yet: " +String Id2String(NAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool NAME in keys(SIGS)

    rule #log(ARGS, @event(EID, EPARAMS)) => #logAux(EID, ARGS, EPARAMS, .Exprs, .EventParams, .Exprs, .EventParams)

    rule #logAux(EID, (ARG1, ARGS), (EPARAM1 EPARAMS), TARGS, TEPARAMS, DARGS, DEPARAMS)
             => #ifThenElse(#isTopic(EPARAM1),
                            #logAux(EID, ARGS, EPARAMS, TARGS ++Expr ARG1, TEPARAMS ++Eparam EPARAM1, DARGS, DEPARAMS),
                            #logAux(EID, ARGS, EPARAMS, TARGS, TEPARAMS, DARGS ++Expr ARG1, DEPARAMS ++Eparam EPARAM1))

    // 0 topic
    rule #logAux(EID, .Exprs, .EventParams, (TARG1, .Exprs), (TEPARAM1 .EventParams), DARGS, DEPARAMS)
           => #log1(#packLoggingData(DARGS, DEPARAMS), EID)

    // 1 topic
    rule #logAux(EID, .Exprs, .EventParams, (TARG1, .Exprs), (TEPARAM1 .EventParams), DARGS, DEPARAMS)
           => #log2(#packLoggingData(DARGS, DEPARAMS),
                    EID,
                    #packLoggingTopic(#resolveExpr(TARG1), TEPARAM1))

    // 2 topics
    rule #logAux(EID, .Exprs, .EventParams, (TARG1, TARG2, .Exprs), (TEPARAM1 TEPARAM2 .EventParams), DARGS, DEPARAMS)
           => #log3(#packLoggingData(DARGS, DEPARAMS),
                    EID,
                    #packLoggingTopic(#resolveExpr(TARG1), TEPARAM1),
                    #packLoggingTopic(#resolveExpr(TARG2), TEPARAM2))

    // 3 topics
    rule #logAux(EID, .Exprs, .EventParams, (TARG1, TARG2, TARG3, .Exprs), (TEPARAM1 TEPARAM2 TEPARAM3 .EventParams), DARGS, DEPARAMS)
           => #log4(#packLoggingData(DARGS, DEPARAMS),
                    EID,
                    #packLoggingTopic(#resolveExpr(TARG1), TEPARAM1),
                    #packLoggingTopic(#resolveExpr(TARG2), TEPARAM2),
                    #packLoggintTopic(#resolveExpr(TARG3), TEPARAM3))


    rule #log1((DATACODE, START, SIZE), EID) => $%seq(
                                                  DATACODE;
                                                  $log1(START, SIZE, EID);.LLLExps);.LLLExps

    rule #log2((DATACODE, START, SIZE), EID, @tlll(_, TOPIC1))
             => $%seq(
                  DATACODE;
                  $log2(START, SIZE, EID, TOPIC1);.LLLExps);.LLLExps

    rule #log3((DATACODE, START, SIZE), EID, @tlll(_, TOPIC1), @tlll(_, TOPIC2))
             => $%seq(
                  DATACODE;
                  $log3(START, SIZE, EID, TOPIC1, TOPIC2);.LLLExps);.LLLExps

    rule #log4((DATACODE, START, SIZE), EID, @tlll(_, TOPIC1), @tlll(_, TOPIC2), @tlll(_, TOPIC3))
             => $%seq(
                  DATACODE;
                  $log4(START, SIZE, EID, TOPIC1, TOPIC2, TOPIC3);.LLLExps);.LLLExps


    syntax CPackedLoggingData ::= "#packLoggingData"    "(" Exprs        ","
                                                            EventParams  ")"
    syntax CPackedLoggingData ::= "#packLoggingDataAux" "(" Exprs        ","
                                                            EventParams  ","
                                                            LLLExps      ","
                                                            Int /*size*/ ")"
 // -----------------------------------------------------------------------------
    rule #packLoggingData(DARGS, DEPARAMS) => #ifThenElse(#numOfExprs(DARGS) ==Int 0,
                                                          ($pass, 0, 0),
                                                          #packLoggingDataAux(DARGS, DEPARAMS, .LLLExps, 0))

    rule #packLoggingDataAux(.Exprs, .EventParams, CODE, SIZE)
             => ($%seq(CODE), #getFirstStoreLoc(CODE), SIZE)

    rule #packLoggingDataAux((DARG, DARGS), %eparam(_, T, _) DEPARAMS, CODE, SIZE)
             => #packArgBy32Base(#baseTypeConvert(#resolveExpr(DARG), T), #newPlaceholder(T))
             ~> #packLoggingDataAux(DARGS, DEPARAMS, CODE, SIZE)
      requires isBaseType(T)

    rule (ARGCODE, ARGSIZE) ~> #packLoggingDataAux(DARGS, DEPARAMS, CODE, TOTALSIZE)
             => #packLoggingDataAux(DARGS, DEPARAMS, CODE ++LLL ARGCODE, TOTALSIZE +Int ARGSIZE)


    syntax CTypedLLLExp ::= "#packLoggingTopic" "(" CTypedLLLExp "," EventParams ")"  [strict(1)]
 // ---------------------------------------------------------------------------------------------
    rule #packLoggingTopic(ARGCODE, %eparam(_, T, _)) => #baseTypeConvert(ARGCODE, T)
      requires isBaseType(T)


///////////////////////////////////////////////////////////////////////////////
// Expressions
///////////////////////////////////////////////////////////////////////////////


    syntax CTypedLLLExp ::= "#resolveExpr" "(" Expr ")"
 // ---------------------------------------------------
    rule #resolveExpr(%self) => @tlll(%address, $address)


    // Number
    rule #resolveExpr(I:Int) => #ifThenElse(
                                  (I >=Int -2 ^Int 127 +Int 1) andBool (I <=Int 2 ^Int 127 -Int 1),
                                  @tlll(%num, I),
                                  #exception("Number out of range")
                                )

    rule #resolveExpr(%hex(STR)) => @tlll(%address, String2Base(STR, 16))
      requires lengthString(STR) ==Int 40

    rule #resolveExpr(%hex(STR)) => @tlll(%bytes32, String2Base(STR, 16))
      requires lengthString(STR) ==Int 64


    // Bool
    rule #resolveExpr(true)  => @tlll(%bool, 1)

    rule #resolveExpr(false)  => @tlll(%bool, 0)


    // Var
    rule #resolveExpr(V) => #unwrapLocation(#lookupVar(V))


    // Reserved Expr
    rule #resolveExpr(%msg.sender)       => @tlll(%address, $caller)

    rule #resolveExpr(%msg.value)        => @tlll(%unitT(%num, %wei, false), $callvalue)

    rule #resolveExpr(%msg.gas)          => @tlll(%num, $gas)

    rule #resolveExpr(%block.difficulty) => @tlll(%num, $difficulty)

    rule #resolveExpr(%block.timestamp)  => @tlll(%unitT(%num, %sec, true), $timestamp)

    rule #resolveExpr(%block.coinbase)   => @tlll(%address, $coinbase)

    rule #resolveExpr(%block.number)     => @tlll(%num, $number)

    rule #resolveExpr(%block.prevhash)   => @tlll(%bytes32, $blockhash($sub($number, 1)))

    rule #resolveExpr(%tx.origin)        => @tlll(%address, $origin)


    // Reserved Func
    rule #resolveExpr(%as_num128(EXPR)) => #asNum128(#resolveExpr(EXPR))

    rule #resolveExpr(%as_num256(EXPR)) => #asNum256(#resolveExpr(EXPR))

    rule #resolveExpr(%as_wei_value(EXPR, UNIT)) => #asWeiValue(#resolveExpr(EXPR), UNIT)

    rule #resolveExpr(%num256_add(LEFTE, RIGHTE)) => #num256Add(#resolveExpr(LEFTE), #resolveExpr(RIGHTE))

    rule #resolveExpr(%num256_sub(LEFTE, RIGHTE)) => #num256Sub(#resolveExpr(LEFTE), #resolveExpr(RIGHTE))


    syntax CTypedLLLExp ::= "#asNum128"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp ::= "#asNum128Aux" "(" LLLExp ")"
 // -----------------------------------------------------------------------
    rule #asNum128(@tlll(T, CODE))
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %num256) orBool #isTypeOf(T, %address),
                            #asNum128Aux(CODE),
                            #exception("Function arg type does not match expected type."))

    rule #asNum128Aux(CODE) => @tlll(%num, $clamp($mload(@minNumPos), CODE, $mload(@maxNumPos)))


    syntax CTypedLLLExp ::= "#asNum256"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp ::= "#asNum256Aux" "(" TypedLLLExp ")"
    syntax CTypedLLLExp ::= "#asNum256ForNumber" "(" LLLExp ")"
    syntax CTypedLLLExp ::= "#asNum256ForLLLExp" "(" LLLExp ")"
 // -----------------------------------------------------------------------
    rule #asNum256(@tlll(T, CODE))
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %address),
                            #asNum256Aux(@tlll(T, CODE)),
                            #exception("Function arg type does not match expected type."))

    rule #asNum256Aux(@tlll(T, CODE)) => #ifThenElse(isInt(CODE),
                                                     #asNum256ForNumber(CODE),
                                                     #asNum256ForLLLExp(CODE))

    rule #asNum256ForNumber(I:Int) => #ifThenElse((I >=Int 0) andBool (I <=Int 2^Int 256 -Int 1),
                                                   @tlll(%num256, I),
                                                   #exception("Number out of range"))

    rule #asNum256ForLLLExp(CODE) => @tlll(%num256, CODE)


    syntax CTypedLLLExp ::= "#asWeiValue"    "(" CTypedLLLExp "," Id  ")"                [strict(1)]
    syntax CTypedLLLExp ::= "#asWeiValueAux" "(" TypedLLLExp  "," Int ")"
    syntax CTypedLLLExp ::= "#asWeiValueForNumber" "(" LLLExp      "," Int ")"
    syntax CTypedLLLExp ::= "#asWeiValueForLLLExp" "(" TypedLLLExp "," Int ")"
 // ------------------------------------------------------------------------------------------------
    rule #asWeiValue(@tlll(T, CODE), UNIT)
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %decimal),
                            #asWeiValueAux(@tlll(T, CODE), #convertToWei(UNIT)),
                            #exception("Function arg type does not match expected type."))

    rule #asWeiValueAux(@tlll(T, CODE), DENOMINATION)
             => #ifThenElse(isInt(CODE),
                            #asWeiValueForNumber(CODE, DENOMINATION),
                            #asWeiValueForLLLExp(@tlll(T, CODE), DENOMINATION))

    rule #asWeiValueForLLLExp(@tlll(%num, CODE), DENOMINATION) => @tlll(%unitT(%num, %wei, false), $mul(CODE, DENOMINATION))

    rule #asWeiValueForLLLExp(@tlll(%decimal, CODE), DENOMINATION)
             => @tlll(%unitT(%num, %wei, false), $div($mul(CODE, DENOMINATION), @decimalDivisor))


    syntax CTypedLLLExp ::= "#num256Add"    "(" CTypedLLLExp "," CTypedLLLExp ")"        [seqstrict]
    syntax CTypedLLLExp ::= "#num256AddAux" "(" LLLExp "," LLLExp ")"
 // ------------------------------------------------------------------------------------------------
    rule #num256Add(@tlll(LT, LCODE), @tlll(RT, RCODE))
            => #ifThenElse(#isTypeOf(LT, %num256) andBool #isTypeOf(RT, %num256),
                           #num256AddAux(LCODE, RCODE),
                           #exception("Function arg type does not match expected type."))

    rule #num256AddAux(LCODE, RCODE)
             => @tlll(%num256, $%seq(
                                 $assert($or($iszero(RCODE), $gt($add(LCODE, RCODE), LCODE)));
                                 $add(LCODE, RCODE);.LLLExps))


    syntax CTypedLLLExp ::= "#num256Sub"    "(" CTypedLLLExp "," CTypedLLLExp ")"        [seqstrict]
    syntax CTypedLLLExp ::= "#num256SubAux" "(" LLLExp "," LLLExp ")"
 // ------------------------------------------------------------------------------------------------
    rule #num256Sub(@tlll(LT, LCODE), @tlll(RT, RCODE))
            => #ifThenElse(#isTypeOf(LT, %num256) andBool #isTypeOf(RT, %num256),
                           #num256SubAux(LCODE, RCODE),
                           #exception("Function arg type does not match expected type."))

    rule #num256SubAux(LCODE, RCODE)
             => @tlll(%num256, $%seq(
                                 $assert($ge(LCODE, RCODE));
                                 $sub(LCODE, RCODE);.LLLExps))


    // Arithmetic
    syntax CTypedLLLExp ::= "#binOp"    "(" BinOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp ::= "#binOpForPure" "(" BinOp "," TypedLLLExp "," TypedLLLExp ")"
 // -----------------------------------------------------------------------------------------------------
    rule #resolveExpr(%binop(BOP, LEFTE, RIGHTE)) => #binOp(BOP, #resolveExpr(LEFTE), #resolveExpr(RIGHTE))

    rule #binOp(BOP, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
                        #exception("Unsupported types for arithmetic op"))
             ~> #ifThenElse(isPureNumType(LT) andBool isPureNumType(RT),
                            #clampArithResult(#binOpForPure(BOP, @tlll(LT, LCODE), @tlll(RT, RCODE))),
                            #exception("Do not support unit type yet."))

    rule #binOpForPure(+, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThenElse(LT ==K RT,
                            @tlll(LT, $add(LCODE, RCODE)),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%decimal, $add($mul(LCODE, @decimalDivisor), RCODE)),
                    #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                                @tlll(%decimal, $add(LCODE, $mul(RCODE, @decimalDivisor))),
                                #exception("How did I get here?"))))

    rule #binOpForPure(-, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThenElse(LT ==K RT,
                            @tlll(LT, $sub(LCODE, RCODE)),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%decimal, $sub($mul(LCODE, @decimalDivisor), RCODE)),
                    #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                                @tlll(%decimal, $sub(LCODE, $mul(RCODE, @decimalDivisor))),
                                #exception("How did I get here?"))))

    rule #binOpForPure(*, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThenElse(LT ==K RT andBool LT ==K %num,
                            @tlll(%num, $mul(LCODE, RCODE)),
                  #ifThenElse(LT ==K RT andBool LT ==K %decimal,
                              @tlll(%decimal, $with($r, RCODE,
                                                $with($l, LCODE,
                                                  $with($ans, $mul($l, $r),
                                                    $%seq(
                                                      $assert($or($eq($sdiv($ans, $l), $r), $not($l)));
                                                      $sdiv($ans, @decimalDivisor);.LLLExps))))),
                    #ifThen((LT ==K %num andBool RT ==K %decimal) orBool (LT ==K %decimal andBool RT ==K %num),
                            @tlll(%decimal, $with($r, RCODE,
                                              $with($l, LCODE,
                                                $with($ans, $mul($l, $r),
                                                  $%seq(
                                                    $assert($or($eq($sdiv($ans, $l), $r), $not($l)));
                                                    $ans;.LLLExps))))))))

    rule #binOpForPure(/, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThenElse(RT ==K %num,
                            @tlll(LT, $sdiv(LCODE, $clamp_nonzero(RCODE))),
                  #ifThenElse(LT ==K RT andBool LT ==K %decimal,
                              @tlll(%decimal, $with($l, LCODE,
                                                $with($r, $clamp_nonzero(RCODE),
                                                  $sdiv($mul($l, @decimalDivisor), $r)))),
                    #ifThen(LT ==K %num andBool RT ==K %decimal,
                            @tlll(%decimal, $sdiv($mul(LCODE, @decimalDivisor ^Int 2), $clamp_nonzero(RCODE))))))


    // Compare
    syntax CTypedLLLExp ::= "#compareOp"    "(" CompareOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp ::= "#compareOpAux" "(" CompareOp "," TypedLLLExp "," TypedLLLExp ")"
 // -------------------------------------------------------------------------------------------------------------
    rule #resolveExpr(%compareop(COP, LEFTE, RIGHTE)) => #compareOp(COP, #resolveExpr(LEFTE), #resolveExpr(RIGHTE))

    rule #compareOp(COP, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
                #ifThen(COP =/=K %eq andBool COP =/=K %ne,
                        #exception("Invalid type for comparison op")))
           ~> #compareOpAux(COP, @tlll(LT, LCODE), @tlll(RT, RCODE))

    rule #compareOpAux(%gt, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $sgt(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $sgt(LCODE, $mul(RCODE, @decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $sgt($mul(LCODE, @decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%ge, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $sge(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $sge(LCODE, $mul(RCODE, @decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $sge($mul(LCODE, @decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%lt, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $slt(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $slt(LCODE, $mul(RCODE, @decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $slt($mul(LCODE, @decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%le, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $sle(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $sle(LCODE, $mul(RCODE, @decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $sle($mul(LCODE, @decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%eq, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $eq(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $eq(LCODE, $mul(RCODE, @decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $eq($mul(LCODE, @decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%ne, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $ne(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $ne(LCODE, $mul(RCODE, @decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $ne($mul(LCODE, @decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))


    // Bool
    syntax CTypedLLLExp ::= "#boolOp" "(" BoolOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp ::= "#boolOpAux" "(" BoolOp "," TypedLLLExp "," TypedLLLExp ")"
 // ----------------------------------------------------------------------------------------------------
    rule #resolveExpr(%boolop(BOP, LEFTE, RIGHTE)) => #boolOp(BOP, #resolveExpr(LEFTE), #resolveExpr(RIGHTE))

    rule #boolOp(BOP, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThenElse((LT ==K %bool) andBool (RT ==K %bool),
                            #boolOpAux(BOP, @tlll(LT, LCODE), @tlll(RT, RCODE)),
                            #exception("Boolean operations can only be between booleans!"))

    rule #boolOpAux(%and, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => @tlll(%bool, $and(LCODE, RCODE))

    rule #boolOpAux(%or, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => @tlll(%bool, $or(LCODE, RCODE))


    // Unary
    syntax CTypedLLLExp ::= "#unaryOp" "(" UnaryOp "," CTypedLLLExp ")"    [strict(2)]
 // ----------------------------------------------------------------------------------
    rule #resolveExpr(%unaryop(UOP, EXPR)) => #unaryOp(UOP, #resolveExpr(EXPR))

    rule #unaryOp(%not, @tlll(T, CODE)) => @tlll(%bool, $iszero(CODE))

    rule #unaryOp(%neg, @tlll(T, CODE)) => #ifThenElse(isNumericType(T),
                                                       @tlll(T, $sub(0, CODE)),
                                                       #exception("Unsupported type for negation."))


    syntax CTypedLLLExp ::= "#clampArithResult" "(" CTypedLLLExp ")"                     [strict]
 // ---------------------------------------------------------------------------------------------
    rule #clampArithResult(@tlll(%num, CODE))
              => @tlll(%num, $clamp($mload(@minNumPos), CODE, $mload(@maxNumPos)))

    rule #clampArithResult(@tlll(%decimal, CODE))
              => @tlll(%decimal, $clamp($mload(@minDecimalPos), CODE, $mload(@maxDecimalPos)))


    syntax CTypedLLLExp ::= "#unwrapLocation" "(" CTypedAddr ")"  [strict]
 // ----------------------------------------------------------------------
    rule #unwrapLocation(@taddr(T, LOC, false, _)) => @tlll(T, $mload(LOC))
    rule #unwrapLocation(@taddr(T, LOC, true, _)) => @tlll(T, $sload(LOC))
   

    syntax CLLLExps    ::= "#convertToLLLExps" "(" CLLLExp ")"    [strict]
 // ----------------------------------------------------------------------
    rule #convertToLLLExps(CODE) => CODE;.LLLExps


    syntax KItem       ::= "#cleanConfig"
 // -------------------------------------
    rule <k> CODE:LLLExps ~> (#cleanConfig => .) ...</k>
         <env> _ => .Map </env>
         <nextMem> _ => @reservedMemPos </nextMem>
         <placeholder> _ => 1 </placeholder>
         <forvar> _ => .Set </forvar>
         <return> _ => %void </return>
         <constant> _ => false </constant>
         <payable> _ => false </payable>                       [structural]


    syntax KItem       ::= "#exception" "(" String ")"
 // --------------------------------------------------


//////////////////////////////////////////////////////////////////////////////
// Utils
//////////////////////////////////////////////////////////////////////////////


    syntax Bool ::= "#isInitFunc" "(" Id ")"    [function]
 // ------------------------------------------------------
    rule #isInitFunc(NAME) => NAME ==K __init__


    syntax Bool ::= "#isTypeOf" "(" Type "," Type /*target type*/ ")"    [function]
 // -------------------------------------------------------------------------------
    rule #isTypeOf(T, TARGET) => #isUnitTypeOf(T, TARGET)
      requires isUnitType(T)

    rule #isTypeOf(T, TARGET) => T ==K TARGET
      requires notBool isUnitType(T)


    syntax Bool ::= "#isUnitTypeOf" "(" UnitType "," Type ")"    [function]
 // -----------------------------------------------------------------------
    rule #isUnitTypeOf(%unitT(T, _, _), T) => true

    rule #isUnitTypeOf(%unitT(T, _, _), TARGET) => false
      requires T =/=K TARGET


    syntax Bool ::= "#isTopic" "(" EventParam ")"    [function]
 // -----------------------------------------------------------
    rule #isTopic(%eparam(_, _, ISTOPIC)) => ISTOPIC


// List Concatenation
// ==================


    syntax Defs  ::= Defs "++Def" Defs    [right, function]
 // ------------------------------------------------------
    rule .Defs ++Def DEFS:Defs => DEFS

    rule (DEF DEFS1) ++Def DEFS2:Defs => DEF (DEFS1 ++Def DEFS2)


    syntax Params ::= Params "++Param" Params    [right, function]
 // -------------------------------------------------------------
    rule .Params ++Param PARAMS:Params => PARAMS

    rule (PARAM PARAMS1) ++Param PARAMS2 => PARAM (PARAMS1 ++Param PARAMS2)


    syntax EventParams ::= EventParams "++Eparam" EventParams    [right, function]
 // -----------------------------------------------------------------------------
    rule .EventParams ++Eparam EPARAMS:EventParams => EPARAMS

    rule (EPARAM EPARAMS1) ++Eparam EPARAMS2 => EPARAM (EPARAMS1 ++Eparam EPARAMS2)


    syntax Exprs  ::= Exprs "++Expr" Exprs    [right, function]
 // ----------------------------------------------------------
    rule .Exprs     ++Expr EXPRS:Exprs => EXPRS

    rule (EXPR , EXPRS1) ++Expr EXPRS2 => EXPR , (EXPRS1 ++Expr EXPRS2)


    syntax LLLExp   ::= "$%seq" "(" LLLExps ")"
    syntax LLLExps  ::= List{LLLExp, ";"}
    syntax LLLExps  ::= LLLExps "++LLL" LLLExps    [right, function]
 // ---------------------------------------------------------------
    rule .LLLExps    ++LLL LES:LLLExps => LES

    rule (LE ; LES1) ++LLL LES2        => LE ; (LES1 ++LLL LES2)


    syntax Ids   ::= List{Id, ""}
    syntax Ids   ::= Ids "++Id" Ids                 [right, function]
    syntax Ids   ::= Ids "++Id" Id                  [right, function]
    syntax Bool  ::= "#inIds" "(" Id "," Ids ")"    [function]
 // ----------------------------------------------------------------
    rule .Ids ++Id IDS:Ids   => IDS

    rule (ID IDS1) ++Id IDS2 => ID (IDS1 ++Id IDS2)

    rule .Ids ++Id ID        => ID .Ids

    rule (ID1 IDS) ++Id ID   => (ID1 IDS) ++Id (ID .Ids)

    rule #inIds(ID, .Ids) => false

    rule #inIds(ID, ID1 IDS) => true               requires ID ==K ID1

    rule #inIds(ID, ID1 IDS) => #inIds(ID, IDS)    requires ID =/=K ID1


    syntax Bool ::= "#inDecorators" "(" Decorator "," Decorators ")"  [function]
 // ----------------------------------------------------------------------------
    rule #inDecorators(D, .Decorators) => false

    rule #inDecorators(D, DEC DECS) => true                     requires D ==K DEC

    rule #inDecorators(D, DEC DECS) => #inDecorators(D, DECS)   requires D =/=K DEC


// Type Related
// ============


    syntax Int       ::= "#sizeOfParams" "(" Params ")"    [function]
    syntax Int       ::= "#sizeOfParam"  "(" Param  ")"    [function]
 // -----------------------------------------------------------------
    rule #sizeOfParams(.Params) => 0

    rule #sizeOfParams(P PS)    => #sizeOfParam(P) +Int #sizeOfParams(PS)

    rule #sizeOfParam(%param(_, %bytesT(_))) => 32

    rule #sizeOfParam(%param(_, T)) => #sizeOfType(T)    requires notBool isByteArrayType(T)


    syntax Int       ::= "#sizeOfType" "(" Type ")"     [function]
 // --------------------------------------------------------------
    rule #sizeOfType(T:BaseType) => 32

    rule #sizeOfType(%bytesT(L)) => #ceil32(L) +Int 64

    rule #sizeOfType(%listT(T, N)) => #sizeOfType(T) *Int N

    rule #sizeOfType(%structT(.VarDecls)) => 0

    rule #sizeOfType(%structT(%vdecl(_, T) VS)) => #sizeOfType(T) +Int #sizeOfType(%structT(VS))


    syntax String    ::= "#canonicalizeType" "(" Type "," Bool /*is event?*/")"  [function]
 // ---------------------------------------------------------------------------------------
    rule #canonicalizeType(%bytesT(L), true) => "bytes" +String Int2String(L)
      requires L <=Int 32

    rule #canonicalizeType(%bytesT(L), true) => "bytes"
      requires notBool(L <=Int 32)

    rule #canonicalizeType(%bytesT(L), false) => "bytes"

    rule #canonicalizeType(%listT(T, N), _) => #canonicalizeType(T, false) +String "[" +String Int2String(N) +String "]"
         requires isBaseType(T) orBool isListType(T)

    rule #canonicalizeType(%num, _) => "int128"

    rule #canonicalizeType(%decimal, _) => "decimal10"

    rule #canonicalizeType(%num256, _) => "uint256"
   
    rule #canonicalizeType(%bool, _) => "bool"
 
    rule #canonicalizeType(%address, _) => "address"
 
    rule #canonicalizeType(%bytes32, _) => "bytes32"


    syntax CTypedLLLExp ::= "#baseTypeConvert" "(" CTypedLLLExp "," Type /*to*/ ")"  [strict(1)]
 // --------------------------------------------------------------------------------------------
    rule #baseTypeConvert(@tlll(FROMT, CODE), TOT)
             => #ifThenElse(notBool(isBaseType(FROMT)) orBool notBool(isBaseType(TOT)),
                            #exception("Base type conversion from or to non-base type."),
                  #ifThenElse(FROMT ==K TOT,
                              @tlll(TOT, CODE),
                    #ifThenElse(FROMT ==K %num andBool TOT ==K %decimal,
                                @tlll(TOT, $mul(CODE, @decimalDivisor)),
                      #ifThenElse(FROMT ==K %num256 andBool TOT ==K %num,
                                  @tlll(TOT, $uclample(CODE, $mload(@maxNumPos))),
                                  #exception("Typecasting unavailable.")))))


// Compute signatures
// ==================


    syntax Int     ::= "#computeEventId"     "(" Id     "," EventParams ")"    [function]
    syntax String  ::= "#computeEventSig"    "(" String "," EventParams ")"    [function]
 // -------------------------------------------------------------------------------------
    rule #computeEventId(NAME, EPARAMS)
        => String2Base(Keccak256(#computeEventSig(Id2String(NAME) +String "(" , EPARAMS)), 16)

    rule #computeEventSig(SIG, %eparam(_, T, _) EPARAM1 EPARAMS)
        => #computeEventSig(SIG +String #canonicalizeType(T, true) +String "," , EPARAM1 EPARAMS)

    rule #computeEventSig(SIG, %eparam(_, T, _) .EventParams)
        => #computeEventSig(SIG +String #canonicalizeType(T, true), .EventParams)

    rule #computeEventSig(SIG, .EventParams) => SIG +String ")"


    syntax Int     ::= "#computeFuncId"  "(" Id     "," Params ")"    [function]
    syntax String  ::= "#computeFuncSig" "(" String "," Params ")"    [function]
 // ----------------------------------------------------------------------------
    rule #computeFuncId(NAME, PARAMS)
        => String2Base(substrString(Keccak256(#computeFuncSig(Id2String(NAME) +String "(", PARAMS)), 0, 8), 16)

    rule #computeFuncSig(SIG, %param(_,T) PARAM1 PARAMS)
        => #computeFuncSig(SIG +String #canonicalizeType(T, false) +String "," , PARAM1 PARAMS)

    rule #computeFuncSig(SIG, %param(_,T) .Params)
        => #computeFuncSig(SIG +String #canonicalizeType(T, false), .Params)

    rule #computeFuncSig(SIG, .Params) => SIG +String ")"


// Memory Lookup and Allocation
// ============================


    syntax CTypedAddr ::= "#lookupVar" "(" Var ")"
 // ----------------------------------------------
    rule <k> #lookupVar(%var(NAME)) => TADDR ... </k>
         <env> %var(NAME) |-> TADDR:TypedAddr ENV </env>

    rule <k> #lookupVar(%var(NAME))
            => #exception("Undeclared Variable: " +String Id2String(NAME)) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in keys(ENV)

    rule <k> #lookupVar(%svar(NAME)) => TADDR ... </k>
         <global> %svar(NAME) |-> TADDR:TypedAddr GLOBAL </global>

    rule <k> #lookupVar(%svar(NAME))
            => #exception("Persistent variable undeclared: " +String Id2String(NAME)) ... </k>
         <global> GLOBAL </global>
      requires notBool %svar(NAME) in keys(GLOBAL)

    rule #lookupVar(%mapelem(V, EXPR))
        => #computeVarOffset(#lookupVar(V), #resolveExpr(EXPR))


    syntax CTypedAddr ::= "#computeVarOffset"    "(" CTypedAddr   /*parent*/ ","
                                                     CTypedLLLExp /*key*/
                                                 ")"                 [seqstrict]
    syntax CTypedAddr ::= "#computeMapVarOffset" "(" CTypedAddr        ","
                                                     CTypedLLLExp
                                                 ")"              [strict(2)]
 // -------------------------------------------------------------------------
    rule #computeVarOffset(@taddr(%mapT(VT, KT), LOC, GLOBAL, MUTABLE), TCODE)
             => #computeMapVarOffset(@taddr(%mapT(VT, KT), LOC, GLOBAL, MUTABLE),
                                     #baseTypeConvert(TCODE, KT))

    rule #computeMapVarOffset(@taddr(%mapT(VT, KT), LOC, true, MUTABLE), @tlll(_, CODE))
             => @taddr(VT, $add($sha3_32(LOC), CODE), true, MUTABLE)

    rule #computeMapVarOffset(@taddr(%mapT(VT, KT), _, false, _), _)
             => #exception("Can only have fixed-side arrays in memory, not mappings")


    syntax CTypedAddr ::= "#newVar" "(" Id "," Type ")"
 // ---------------------------------------------------
    rule <k> #newVar(NAME, T) => @taddr(T, LOC, false, true) ...</k>
         <env> ENV => #updateEnv(ENV, %var(NAME), T, LOC, true) </env>
         <nextMem> LOC => LOC +Int #sizeOfType(T) </nextMem>
      requires notBool %var(NAME) in keys(ENV)

    rule <k> #new(NAME, T)
           => #exception("Duplicate variable name: " +String Id2String(NAME)) ...</k>
         <env> ENV </env>
      requires %var(NAME) in keys(ENV)


    syntax CTypedAddr ::= "#lookupOrNewVar" "(" Var "," Type ")"
 // --------------------------------------------------------------
    rule <k> #lookupOrNewVar(%var(NAME), _) => TADDR ... </k>
         <env> %var(NAME) |-> TADDR:TypedAddr ENV </env>

    rule <k> #lookupOrNewVar(%var(NAME), T) => #newVar(NAME, T) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in keys(ENV)

    rule #lookupOrNewVar(%svar(NAME), _) => #lookupVar(%svar(NAME))

    rule #lookupOrNewVar(%mapelem(V, EXPR), _) => #lookupVar(%mapelem(V, EXPR))


    syntax CTypedAddr ::= "#newLoopVar" "(" Id ")"
 // ----------------------------------------------
    rule <k> #newLoopVar(NAME) => #lookupVar(%var(NAME)) ... </k>
         <forvar> FORNAMES </forvar>
      requires NAME in FORNAMES

    rule <k> #newLoopVar(NAME) => #newVar(NAME, %num) ... </k>
         <forvar> FORNAMES (.Set => SetItem(NAME)) </forvar>
      requires notBool NAME in FORNAMES


    syntax CTypedAddr ::= "#newPlaceholder" "(" Type ")"
 // ----------------------------------------------------
    rule <k> #newPlaceholder(T)
           => #newVar(String2Id("_placeholder_" +String Int2String(I)), T) ... </k>
         <placeholder> I => I +Int 1 </placeholder>


    syntax Map  ::= "#updateEnv" "(" Map "," Var "," Type "," Int /*loc*/ "," Bool /*mutable*/ ")"  [function]
    syntax Map  ::= "#flattenStruct" "(" Map "," Var "," VarDecls "," Int "," Bool ")"              [function]
 // ----------------------------------------------------------------------------------------------------------
    rule #updateEnv(M, V, %structT(VARDECLS), LOC, ISMUTABLE) => #flattenStruct(M, V, VARDECLS, LOC, ISMUTABLE)

    rule #updateEnv(M, V, T, LOC, ISMUTABLE) => M[V <- @taddr(T, LOC, false, ISMUTABLE)]
      requires notBool isStructType(T)

    rule #flattenStruct(M, V, .VarDecls, LOC, ISMUTABLE) => M

    rule #flattenStruct(M, V, %vdecl(NAME, T) VS, LOC, ISMUTABLE)
        => #flattenStruct(#updateEnv(M, %mem(V, NAME), T, LOC, ISMUTABLE),
                          V, VS, LOC +Int #sizeOfType(T), ISMUTABLE)



// Others
// ============================


    syntax Int    ::= "#convertToWei" "(" Id ")"    [function]
 // ----------------------------------------------------------
    rule #convertToWei(wei)      => 1

    rule #convertToWei(kwei)     => 10 ^Int 3

    rule #convertToWei(ada)      => 10 ^Int 3

    rule #convertToWei(lovelace) => 10 ^Int 3

    rule #convertToWei(babbage)  => 10 ^Int 6

    rule #convertToWei(shannon)  => 10 ^Int 9

    rule #convertToWei(gwei)     => 10 ^Int 9

    rule #convertToWei(szabo)    => 10 ^Int 12

    rule #convertToWei(finney)   => 10 ^Int 15

    rule #convertToWei(ether)    => 10 ^Int 18


    syntax KItem  ::= "#ifThen" "(" Bool /*condition*/ "," K /*then*/ ")"    [function]
 // -----------------------------------------------------------------------------------
    rule #ifThen(true, THENCLAUSE) => THENCLAUSE
    rule #ifThen(false, THENCLAUSE) => .


    syntax KItem  ::= "#ifThenElse" "(" Bool /*condition*/ "," K /*then*/ "," K /*else*/ ")"    [function]
 // ------------------------------------------------------------------------------------------------------
    rule #ifThenElse(true, THENCLAUSE, ELSECLAUSE) => THENCLAUSE
    rule #ifThenElse(false, THENCLAUSE, ELSECLAUSE) => ELSECLAUSE


    syntax Int    ::= "#numOfExprs" "(" Exprs ")"
 // ---------------------------------------------
    rule #numOfExprs(.Exprs) => 0

    rule #numOfExprs(EXPR, EXPRS) => 1 +Int #numOfExprs(EXPRS)


    syntax CPackedArgBy32 ::= "#packArgBy32Base" "(" CTypedLLLExp ","
                                                     CTypedAddr   ")"     [seqstrict]
 // ---------------------------------------------------------------------------------
    rule #packArgBy32Base(@tlll(_, CODE), @taddr(_, LOC:Int, _, _)) => ($mstore(LOC, CODE); .LLLExps, 32)


    syntax Int ::= "#getFirstStoreLoc" "(" LLLExps ")"  [function]
 // --------------------------------------------------------------
    rule #getFirstStoreLoc($mstore(L:Int, _); CODE) => L


endmodule
