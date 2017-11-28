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
        <inLoop> .Set </inLoop>  // In Loop status. Whether body is currently evaluating within a for-loop or not.
    </T>


///////////////////////////////////////////////////////////////////////////////
// Data Types
///////////////////////////////////////////////////////////////////////////////


    syntax Type        ::= "%mixedT"

    syntax LocTarget   ::= "@storage" | "@memory" | "@storage_prehashed"

    syntax LocAttr     ::= "@locattr" "(" LocTarget "," Bool /*mutable?*/ ")"

    syntax LLLExpAttr  ::= LocAttr
                         | "@none"  // @none means an LLLExp represents a value rather than a storage/memory location

    syntax TypedAddr   ::= "@taddr" "(" Type ","
                                        LLLExp /*loc*/    ","
                                        LocAttr           ")"

    syntax TypedLLLExp  ::= "@tlll"  "(" Type              ","
                                         LLLExp            ","
                                         LLLExpAttr        ")"  // If an exp has @storage/@memory target, it represents a location.
                                                                // You need to call `#unwrapLoc` function to read value from the location.
    syntax TypedLLLExps ::= List{TypedLLLExp, ""}

    syntax EventRecord ::= "@event" "(" Int /*event_id*/  ","
                                        Id  /*name*/      ","
                                        EventParams       ")"

    syntax FuncRecord  ::= "@func" "(" Int /*func_id*/    ","
                                       Id  /*name*/       ","
                                       Params             ","
                                       Type               ","
                                       Bool /*constant?*/ ","
                                       Bool /*payable?*/  ","
                                       Bool /*internal?*/ ")"

    syntax PackedLoggingData  ::= "@loggingdata" "(" LLLExp ","  // code
                                                     Int    ","  // start loc
                                                     Int    ")"  // size

    syntax PackedArgBy32      ::= "@argby32" "(" LLLExps ","  // code
                                                 Int     ")"  // size

    syntax PackedArgData      ::= "@argdata" "(" LLLExp ","  // code
                                                 Int    ")"  // size

    // Convention: C'Sort' is a one-one corresponding supersort of Sort. C'Sort'
    //             requires for evaluation (i.e. not KResult).
    syntax CLLLExp             ::= LLLExp
    syntax CLLLExps            ::= LLLExps
    syntax CTypedLLLExp        ::= TypedLLLExp
    syntax CPackedLoggingData  ::= PackedLoggingData
    syntax CPackedArgBy32      ::= PackedArgBy32
    syntax CPackedArgData      ::= PackedArgData

    syntax KResult  ::= LLLExp
                      | LLLExps
                      | TypedLLLExp
                      | PackedLoggingData
                      | PackedArgBy32
                      | PackedArgData
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
                      ($%seq(INITIALIZER),.LLLExps) ++LLL INITFUNC ++LLL
                      ($return(
                         0,
                         $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0)),.LLLExps)
                    ) </lll>

    rule <k> #compileViperToLLLAux(INITIALIZER, OTHERFUNCS) => . ... </k>
         <lll> _ => $%seq(
                      $return(
                        0,
                        $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0)),.LLLExps
                    ) </lll>


// Process Events
// ==============


    syntax KItem  ::= "#addEvents"     "(" Events ")"
    syntax KItem  ::= "#addEvent"      "(" Event ")"
    syntax KItem  ::= "#addEventAux"   "(" Id "," EventParams ")"
 // -------------------------------------------------------------
    rule #addEvents(.Events) => .

    rule #addEvents(E ES) => #addEvent(E) ~> #addEvents(ES)

    rule <k> #addEvent(%event(NAME, EPARAMS))
            => #checkEventParams(EPARAMS, 0, .Ids)
            ~> #addEventAux(NAME, EPARAMS)
         ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool NAME in keys(SIGS)

    rule <k> #addEvent(%event(NAME, EPARAMS))
            => #exception("Duplicate event name: " +String Id2String(NAME))
         ... </k>
         <internalSig> SIGS </internalSig>
      requires NAME in keys(SIGS)

    rule <k> #addEventAux(NAME, EPARAMS) => . ... </k>
         <internalSig> SIGS
                      => SIGS[NAME <- @event(#computeEventId(NAME, EPARAMS), NAME, EPARAMS)] </internalSig>


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
         <global> GLOBALS => GLOBALS[%svar(NAME) <- @taddr(T, LOC, @locattr(@storage, true))] </global>
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
 // ----------------------------------------------------------------
    rule #addFuncs(.Defs) => .

    rule #addFuncs(%fdecl(DECS, FNAME, PARAMS, T, STMTS) DEFS)
        => #addFunc(FNAME, PARAMS, T,
                    #inDecorators(%@constant, DECS),
                    #inDecorators(%@payable, DECS),
                    #inDecorators(%@internal, DECS),
                    #inDecorators(%@public, DECS))
        ~> #addFuncs(DEFS)

    rule #addFunc(FNAME, PARAMS, T, CONSTANT, PAYABLE, INTERNAL, PUBLIC)
        => #checkFuncParams(PARAMS, .Ids)
        ~> #checkInternalPublicMECE(INTERNAL, PUBLIC)
        ~> #addFuncAux(FNAME, PARAMS, T, CONSTANT, PAYABLE, INTERNAL)

    rule <k> #addFuncAux(FNAME, PARAMS, T, CONSTANT, PAYABLE, INTERNAL) => . ... </k>
         <internalSig> SIGS
                      => SIGS[FNAME <- @func(#computeFuncId(FNAME, PARAMS),
                                             FNAME,
                                             PARAMS,
                                             T,
                                             CONSTANT,
                                             PAYABLE,
                                             INTERNAL)] </internalSig>
      requires notBool FNAME in keys(SIGS)

    rule <k> #addFuncAux(FNAME, _, _, _, _, _)
        => #exception("Duplicate event or function name: " +String Id2String(FNAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires FNAME in keys(SIGS)


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
 // ------------------------------------------------------------------------------------------
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


    syntax Defs  ::= "#mkPublicGetterBase"      "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterByteArray" "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterListT"     "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterMapT"      "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterStructT"   "(" String "," Params "," Type "," Var "," Int ")"  [function]
 // -------------------------------------------------------------------------------------------------------------
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
                               $mstore(28 , $calldataload(0)),
                               $mstore(@addrSizePos, @addrSize),
                               $mstore(@maxNumPos, @maxNum),
                               $mstore(@minNumPos, @minNum),
                               $mstore(@maxDecimalPos, @maxDecimal),
                               $mstore(@minDecimalPos, @minDecimal),.LLLExps),.LLLExps


///////////////////////////////////////////////////////////////////////////////
// Function Definitions
///////////////////////////////////////////////////////////////////////////////


    syntax CLLLExps  ::= "#compileFuncs" "(" Defs "," LLLExps ")"
 // ------------------------------------------------------------
    rule #compileFuncs(.Defs, RESULTCODE) => RESULTCODE

    rule #compileFuncs(DEF DEFS, RESULTCODE) => #compileFunc(DEF) ~> #compileFuncs(DEFS, RESULTCODE)

    rule (FUNCCODE:LLLExps ~> #compileFuncs(DEFS, RESULTCODE))
        => #compileFuncs(DEFS, RESULTCODE ++LLL FUNCCODE)


    syntax CLLLExps  ::= "#compileFunc"    "(" Def  ")"
    syntax CLLLExps  ::= "#compileFuncAux" "(" CLLLExps /*copy input*/      ","
                                               CLLLExps /*check decorator*/ ","
                                               CLLLExps /*fill params*/     ","
                                               CLLLExps /*compile stmts*/   ","
                                               Int      /*func id*/         ","
                                               Bool     /*init?*/
                                           ")"                      [seqstrict]
 // ---------------------------------------------------------------------------
    rule <k> #compileFunc(%fdecl(DECS, FNAME, PARAMS, T, STMTS))
            => #compileFuncAux(#copyArg(PARAMS, #isInitFunc(FNAME)),
                               #addClampersForDecorators(PAYABLE, INTERNAL),
                               #fillParams(PARAMS, 0, #isInitFunc(FNAME), .LLLExps),
                               #compileStmts(STMTS, .LLLExps),
                               FUNCID,
                               #isInitFunc(FNAME))
           ~> #cleanConfig ... </k>
         <internalSig> FNAME |-> @func(FUNCID, FNAME, _, T, CONSTANT, PAYABLE, INTERNAL) SIGS</internalSig>
         <return> _ => T </return>
         <constant> _ => CONSTANT </constant>
         <payable> _ => PAYABLE </payable>


    rule #compileFuncAux(COPYARG, CHECKDECS, FILLPARAMS, STMTS, _, true)
        => $%seq(COPYARG ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL ($%seq(STMTS),.LLLExps)),.LLLExps

    rule #compileFuncAux(COPYARG, CHECKDECS, FILLPARAMS, STMTS, FUNCID, false)
        => $if(
             $eq($mload(0), FUNCID),
             $%seq(COPYARG ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL STMTS ++LLL ($stop,.LLLExps))),.LLLExps


// Copy Arguments
// ==============


    syntax CLLLExps  ::= "#copyArg" "(" Params "," Bool /*init?*/ ")"
 // -----------------------------------------------------------------
    rule #copyArg(.Params, _) => $pass,.LLLExps

    rule <k> #copyArg(PARAMS, true) => $codecopy(@reservedMemPos,
                                                 $codelen,
                                                 #sizeOfParams(PARAMS)),.LLLExps ... </k>
         <nextMem> M => M +Int #sizeOfParams(PARAMS) </nextMem>
      requires #sizeOfParams(PARAMS) >Int 0

    rule <k> #copyArg(PARAMS, false) => $calldatacopy(@reservedMemPos,
                                                      4,
                                                      #sizeOfParams(PARAMS)),.LLLExps ... </k>
         <nextMem> M => M +Int #sizeOfParams(PARAMS) </nextMem>
      requires #sizeOfParams(PARAMS) >Int 0


// Add Clampers For Decorators
// ===========================


    syntax CLLLExps  ::= "#addClampersForDecorators" "(" Bool "," Bool ")"
    syntax LLLExps   ::= "#checkPayable"    "(" Bool ")"        [function]
    syntax LLLExps   ::= "#checkInternal"   "(" Bool ")"        [function]
 // ----------------------------------------------------------------------
    rule #addClampersForDecorators(PAYABLE, INTERNAL) => #checkPayable(PAYABLE) ++LLL #checkInternal(INTERNAL)

    rule #checkPayable(true) => .LLLExps

    rule #checkPayable(false) => $assert($iszero($callvalue)),.LLLExps

    rule #checkInternal(true) => $assert($eq($caller, $address)),.LLLExps

    rule #checkInternal(false) => .LLLExps


// Fill Parameters
// ===============


    syntax CLLLExps  ::= "#fillParams" "(" Params "," Int /*data pos*/ "," Bool /*init?*/ "," LLLExps ")"
 // -----------------------------------------------------------------------------------------------------
    rule #fillParams(.Params, _, _, RESULTCODE) => RESULTCODE

    rule #fillParams(P PS, DATAPOS, ISINIT, RESULTCODE)
        => #fillParam(P, DATAPOS, ISINIT) ~> #fillParams(PS, DATAPOS +Int #sizeOfParam(P), ISINIT, RESULTCODE)

    rule (FILLCODE:LLLExps ~> #fillParams(PS, DATAPOS, ISINIT, RESULTCODE))
        => #fillParams(PS, DATAPOS, ISINIT, RESULTCODE ++LLL FILLCODE)


    syntax CLLLExps  ::= "#fillParam"  "(" Param  "," Int "," Bool ")"
 // ------------------------------------------------------------------
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
                                                   $mload(@maxNumPos)),.LLLExps

    rule #mkClamper(%unitT(%num, _, _), DPOS, MPOS, ISINIT) => $clamp(
                                                                 $mload(@minNumPos),
                                                                 #mkDataDecl(DPOS, ISINIT),
                                                                 $mload(@maxNumPos)),.LLLExps

    rule #mkClamper(%bool, DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), 2),.LLLExps

    rule #mkClamper(%address, DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), $mload(@addrSizePos)),.LLLExps

    rule #mkClamper(%bytesT(L), DPOS, MPOS, ISINIT)
        => $%seq(
             #mkCopier(MPOS, #mkDataDecl(DPOS, ISINIT), 32 +Int L, ISINIT),
             $assert(
               $le(
                 $calldataload($add(4, #mkDataDecl(DPOS, ISINIT))),
                 L)),.LLLExps),.LLLExps

    rule #mkClamper(%listT(T, N), DPOS, MPOS, ISINIT) => $%seq(#mkClamperListT(N, T, DPOS, MPOS, ISINIT)),.LLLExps

    rule #mkClamperListT(1, T, DPOS, MPOS, ISINIT) => #mkClamper(T, DPOS, MPOS, ISINIT)

    rule #mkClamperListT(N, T, DPOS, MPOS, ISINIT)
             => #mkClamper(T, DPOS, MPOS, ISINIT) ++LLL
                #mkClamperListT(N -Int 1, T, DPOS +Int #sizeOfType(T), MPOS +Int #sizeOfType(T), ISINIT)
      requires N >Int 1

    rule #mkClamper(%decimal, _, _, _) => $pass,.LLLExps

    rule #mkClamper(%unitT(%decimal, _, _), _, _, _) => $pass,.LLLExps

    rule #mkClamper(%num256, _, _, _) => $pass,.LLLExps

    rule #mkClamper(%bytes32, _, _, _) => $pass,.LLLExps

    rule #mkClamper(%mapT(_, _), _, _, _) => $pass,.LLLExps

    rule #mkClamper(%structT(_), _, _, _) => $pass,.LLLExps

    rule #mkCopier(MPOS, POS, SIZE, true) => $codecopy(MPOS, $add($codelen, POS), SIZE)

    rule #mkCopier(MPOS, POS, SIZE, false) => $calldatacopy(MPOS, $add(4, POS), SIZE)

    rule #mkDataDecl(DATAPOS, true) => $codeload($add($codelen, DATAPOS))

    rule #mkDataDecl(DATAPOS, false) => $calldataload($add(4, DATAPOS))


// Clean configuartion
// ===================


    syntax KItem  ::= "#cleanConfig"
 // --------------------------------
    rule <k> CODE:LLLExps ~> (#cleanConfig => .) ...</k>
         <env> _ => .Map </env>
         <nextMem> _ => @reservedMemPos </nextMem>
         <forvar> _ => .Set </forvar>
         <return> _ => %void </return>
         <constant> _ => false </constant>
         <payable> _ => false </payable>
         <placeholder> _ => 1 </placeholder>
         <inLoop> _ => .Set </inLoop>


///////////////////////////////////////////////////////////////////////////////
// Stmts
///////////////////////////////////////////////////////////////////////////////


    syntax CLLLExps  ::= "#compileStmts" "(" Stmts "," LLLExps ")"
 // --------------------------------------------------------------
    rule #compileStmts(.Stmts, RESULTCODE) => RESULTCODE

    rule #compileStmts(STMT STMTS, RESULTCODE) => #compileStmt(STMT) ~> #compileStmts(STMTS, RESULTCODE)

    rule (STMTCODE:LLLExps ~> #compileStmts(STMTS, RESULTCODE))
        => #compileStmts(STMTS, RESULTCODE ++LLL STMTCODE)


    syntax CLLLExps  ::= "#compileStmt" "(" Stmt ")"
 // ------------------------------------------------


// Annotated Assignment
// ====================


    rule #compileStmt(%vdecl(NAME, T)) => #newVar(NAME, T) ~> $pass,.LLLExps

    rule (@tlll(T, LOC, LOCATTR) => .) ~> $pass,.LLLExps


// Assignment
// ==========


    rule #compileStmt(%assign(V, E)) => #assign(V, #compileExpr(E))


    syntax CLLLExps  ::= "#assign"    "(" Var                             ","
                                          CTypedLLLExp  /*compiled Expr*/
                                      ")"                         [strict(2)]

    syntax CLLLExps  ::= "#assignAux" "(" CTypedLLLExp /*variable address*/ ","
                                          TypedLLLExp
                                      ")"                           [strict(1)]
 // ---------------------------------------------------------------------------
    rule #assign(V, @tlll(T, CODE, EXPRATTR))
        => #assignAux(#getTarget(V, #lookupOrNewVar(V, T)),
                      @tlll(T, CODE, EXPRATTR))

    rule #assignAux(LTCODE, RTCODE) => #mkSetter(LTCODE, RTCODE)


    syntax CTypedLLLExp  ::= "#getTarget" "(" Var "," CTypedLLLExp ")"  [strict(2)]
    syntax CTypedLLLExp  ::= "#getTargetAux" "(" TypedLLLExp ")"
 // -------------------------------------------------------------------------------
    rule <k> #getTarget(%var(NAME), TCODE)
            => #exception("Altering iterator which is in use!") ... </k>
         <forvar> FORVARS </forvar>
      requires %var(NAME) in FORVARS

    rule <k> #getTarget(%var(NAME), TCODE) => #getTargetAux(TCODE) ... </k>
         <forvar> FORVARS </forvar>
      requires notBool %var(NAME) in FORVARS

    rule #getTarget(%svar(NAME), TCODE) => #getTargetAux(TCODE)

    rule #getTarget(%mem(V, FIELD), TCODE) => #getTargetAux(TCODE)

    rule <k> #getTarget(%listelem(V, INDEX), TCODE)
            => #exception("Altering list while being iterated!") ... </k>
         <inLoop> INLOOP </inLoop>
      requires V in INLOOP

    rule <k> #getTarget(%listelem(V, INDEX), TCODE) => #getTargetAux(TCODE) ... </k>
         <inLoop> INLOOP </inLoop>
      requires notBool V in INLOOP

    rule #getTarget(%mapelem(V, INDEX), TCODE) => #getTargetAux(TCODE)

    rule <k> #getTargetAux(@tlll(T, LOC, @locattr(TARGET, MUTABLE)))
            => #ifThen(TARGET ==K @storage andBool CONSTANT ==K true,
                       #exception("Cannot modify storage inside a constant function!"))
            ~> #ifThen(MUTABLE ==K false,
                       #exception("Cannot modify function argument"))
            ~> @tlll(T, LOC, @locattr(TARGET, MUTABLE))
         ... </k>
         <constant> CONSTANT </constant>


    syntax CLLLExps  ::= "#mkSetter" "(" CTypedLLLExp  /*left variable loc*/  ","
                                         CTypedLLLExp /*right compiled Expr*/ ")"  [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #mkSetter(@tlll(LT, LOC, LOCATTR), RTCODE)
        => #mkSetterBase(@tlll(LT, LOC, LOCATTR),
                         #baseTypeConvert(RTCODE, LT))
      requires isBaseType(LT)

    rule #mkSetter(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
        => #ifThenElse(notBool(isListType(RT)),
                       #exception("Setter type mismatch: left side is array but right side is not."),
             #ifThenElse(#getListTCount(LT) =/=K #getListTCount(RT),
                         #exception("Mismatched number of elements in left and right side arrays."),
                         #mkSetterListT(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))))
       requires isListType(LT)


    // Basic Types
    syntax CLLLExps  ::= "#mkSetterBase"  "(" CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict]
 // ----------------------------------------------------------------------------------------

    rule #mkSetterBase(@tlll(_, LOC, @locattr(@storage, _)), @tlll(_, CODE, _))
        => $sstore(LOC, CODE),.LLLExps

    rule #mkSetterBase(@tlll(_, LOC, @locattr(@memory, _)), @tlll(_, CODE, _))
        => $mstore(LOC, CODE),.LLLExps

    // TODO: figure out an efficient way to copy byte array


    // Can't copy mappings
    rule #mkSetter(@tlll(LT, LOC, LOCATTR), RTCODE)
        => #exception("Cannot copy mappings; can only copy individual elements.")
      requires isMappingType(LT)


    // List
    syntax CLLLExps  ::= "#mkSetterListT" "(" TypedLLLExp "," TypedLLLExp ")"

    syntax CLLLExps  ::= "#mkSetterListTAux" "(" TypedLLLExp ","  // left
                                                 TypedLLLExp ","  // left token
                                                 TypedLLLExp ")"  // right
 // ----------------------------------------------------------------------------
    rule #mkSetterListT(@tlll(LT, LCODE, @locattr(@storage, MUTABLE)), RTCODE)
        => #mkSetterListTAux(@tlll(LT, $sha3_32(LCODE), @locattr(@storage, MUTABLE)),
                             @tlll(LT, $_L, @locattr(@storage_prehashed, MUTABLE)),
                             RTCODE)

    rule #mkSetterListT(@tlll(LT, LCODE, @locattr(TARGET, MUTABLE)), RTCODE)
        => #mkSetterListTAux(@tlll(LT, LCODE, @locattr(TARGET, MUTABLE)),
                             @tlll(LT, $_L, @locattr(TARGET, MUTABLE)),
                             RTCODE)
      requires TARGET =/=K @storage

    rule #mkSetterListTAux(LCODE, LTOKENCODE, @tlll(RT, RCODE, RLOCATTR))
        => #mkSetterListTLiteral(LCODE, LTOKENCODE, 0, @tlll(RT, RCODE, RLOCATTR), .LLLExps)
      requires isMultiLLLExp(RCODE)

    rule #mkSetterListTAux(LCODE, LTOKENCODE, @tlll(RT, RCODE, RLOCATTR))
        => #mkSetterListTVar(LCODE, LTOKENCODE, 0,
                             @tlll(RT, RCODE, RLOCATTR),
                             @tlll(RT, $_R, RLOCATTR),
                             .LLLExps)
      requires notBool isMultiLLLExp(RCODE)


    syntax CLLLExps  ::= "#mkSetterListTLiteral" "(" TypedLLLExp  ","  // left
                                                     TypedLLLExp  ","  // left token
                                                     Int          ","  // index
                                                     TypedLLLExp  ","  // right
                                                     LLLExps      ")"  // result code
 // -------------------------------------------------------------------------------
    rule #mkSetterListTLiteral(LTCODE, LTOKENCODE, INDEX,
                               @tlll(%listT(T, N), $multi(TEXPR TEXPRS), EXPRATTR), RESULTCODE)
        => #mkSetter(#addVarOffset(LTOKENCODE, @tlll(%num, INDEX, @none)),
                     TEXPR)
        ~> #mkSetterListTLiteral(LTCODE, LTOKENCODE, INDEX,
                                 @tlll(%listT(T, N), $multi(TEXPRS), EXPRATTR), RESULTCODE)
      requires INDEX <Int N

    rule #mkSetterListTLiteral(@tlll(%listT(T, N), LOC, _), _, INDEX, _, RESULTCODE)
        => $with($_L, LOC, $%seq(RESULTCODE)),.LLLExps
      requires INDEX ==Int N

    rule CODE:LLLExps ~> #mkSetterListTLiteral(LTCODE, LTOKENCODE, INDEX, RTCODE, RESULTCODE)
        => #mkSetterListTLiteral(LTCODE, LTOKENCODE, INDEX +Int 1, RTCODE, RESULTCODE ++LLL CODE)


    syntax CLLLExps  ::= "#mkSetterListTVar" "(" TypedLLLExp ","  // left
                                                 TypedLLLExp ","  // left token
                                                 Int         ","  // index
                                                 TypedLLLExp ","  // right
                                                 TypedLLLExp ","  // right token
                                                 LLLExps     ")"  // result code
  // --------------------------------------------------------------------------------
     rule #mkSetterListTVar(@tlll(%listT(T, N), LLOC, LOCATTR), LTOKENCODE, INDEX, RTCODE, RTOKENCODE, RESULTCODE)
         => #mkSetter(#addVarOffset(LTOKENCODE, @tlll(%num, INDEX, @none)),
                      #addVarOffset(RTOKENCODE, @tlll(%num, INDEX, @none)))
         ~> #mkSetterListTVar(@tlll(%listT(T, N), LLOC, LOCATTR), LTOKENCODE, INDEX, RTCODE, RTOKENCODE, RESULTCODE)
       requires INDEX <Int N

     rule #mkSetterListTVar(@tlll(%listT(T, N), LLOC, _), _, INDEX, @tlll(_, RLOC, _), _, RESULTCODE)
         => $with($_L, LLOC, $with($_R, RLOC, $%seq(RESULTCODE))),.LLLExps
       requires INDEX ==Int N

     rule CODE:LLLExps ~> #mkSetterListTVar(LTCODE, LTOKENCODE, INDEX, RTCODE, RTOKENCODE, RESULTCODE)
         => #mkSetterListTVar(LTCODE, LTOKENCODE, INDEX +Int 1, RTCODE, RTOKENCODE, RESULTCODE ++LLL CODE)


// Aug Assignment
// ==============


    rule #compileStmt(%augassign(OP, V, E)) => #augassign(OP,
                                                          #getTarget(V, #compileLocExpr(V)),
                                                          #compileValueExpr(E))


    syntax CLLLExps  ::= "#augassign"    "(" AugAssignOp                    ","
                                             CTypedLLLExp  /*variable loc*/ ","
                                             CTypedLLLExp /*compiled expr*/
                                         ")"                   [seqstrict(2,3)]

    syntax CLLLExps  ::= "#augassignAux" "(" AugAssignOp                    ","
                                             CTypedLLLExp                   ","
                                             TypedLLLExp                    ")"
 // ---------------------------------------------------------------------------
    rule #augassign(OP, @tlll(LT, LOC, @locattr(TARGET, MUTABLE)), RTCODE)
        => #ifThen(notBool(isBaseType(LT)),
                   #exception("Can only use aug-assign operators with simple types!"))
        ~> #augassignAux(OP, @tlll(LT, LOC, @locattr(TARGET, MUTABLE)), RTCODE)

    rule #augassignAux(OP, @tlll(LT, LOC, @locattr(@storage, MUTABLE)), RTCODE)
        => #desugarAugAssign(@tlll(LT, LOC, @locattr(@storage, MUTABLE)),
                             #convertToBinaryArith(OP, @tlll(LT, $sload($_stloc), @none), RTCODE))

    rule #augassignAux(OP, @tlll(LT, LOC, @locattr(@memory, MUTABLE)), RTCODE)
        => #desugarAugAssign(@tlll(LT, LOC, @locattr(@memory, MUTABLE)),
                             #convertToBinaryArith(OP, @tlll(LT, $mload($_mloc), @none), RTCODE))


    syntax CTypedLLLExp  ::= "#convertToBinaryArith" "(" AugAssignOp           ","
                                                         TypedLLLExp  /*left*/ ","
                                                         TypedLLLExp  /*right*/")"
 // ------------------------------------------------------------------------------
    rule #convertToBinaryArith(+=, LTCODE, RTCODE) => #binOp(+, LTCODE, RTCODE)

    rule #convertToBinaryArith(-=, LTCODE, RTCODE) => #binOp(-, LTCODE, RTCODE)

    rule #convertToBinaryArith(*=, LTCODE, RTCODE) => #binOp(*, LTCODE, RTCODE)

    rule #convertToBinaryArith(/=, LTCODE, RTCODE) => #binOp(/, LTCODE, RTCODE)

    rule #convertToBinaryArith(%=, LTCODE, RTCODE) => #binOp(%, LTCODE, RTCODE)


    syntax CLLLExps  ::= "#desugarAugAssign"    "(" TypedLLLExp  ","
                                                    CTypedLLLExp
                                                ")"      [strict(2)]

    syntax CLLLExps  ::= "#desugarAugAssignAux" "(" Int  /*loc*/ ","
                                                    LocTarget    ","
                                                    CTypedLLLExp
                                                ")"      [strict(3)]
 // ----------------------------------------------------------------
    rule #desugarAugAssign(@tlll(LT, LOC, @locattr(TARGET, MUTABLE)), RTCODE)
        => #desugarAugAssignAux(LOC, TARGET, #baseTypeConvert(RTCODE, LT))

    rule #desugarAugAssignAux(LOC, @storage, @tlll(_, CODE, _))
        => $with($_stloc, LOC, $sstore($_stloc, CODE)),.LLLExps

    rule #desugarAugAssignAux(LOC, @memory, @tlll(_, CODE, _))
        => $with($_mloc, LOC, $mstore($_mloc, CODE)),.LLLExps


// If...Then...(Else)
// ==================


    syntax CLLLExps  ::= "#if" "(" CTypedLLLExp /*TEST*/ ","
                                   CLLLExps     /*Then*/ ","
                                   CLLLExps     /*Else*/
                               ")"               [seqstrict]

    syntax CLLLExps  ::= "#if" "(" CTypedLLLExp /*TEST*/ ","
                                   CLLLExps     /*Then*/
                               ")"               [seqstrict]
 // --------------------------------------------------------
    rule #compileStmt(%if(TEST, THENSTMTS, ELSESTMTS)) => #if(#compileValueExpr(TEST),
                                                              #compileStmts(THENSTMTS, .LLLExps),
                                                              #compileStmts(ELSESTMTS, .LLLExps))

    rule #compileStmt(%if(TEST, THENSTMTS)) => #if(#compileValueExpr(TEST), #compileStmts(THENSTMTS, .LLLExps))

    rule #if(@tlll(_, CODE, _), THEN:LLLExps, ELSE:LLLExps) => $if(CODE, $%seq(THEN), $%seq(ELSE)),.LLLExps

    rule #if(@tlll(_, CODE, _), THEN:LLLExp) => $if(CODE, $%seq(THEN)),.LLLExps


// For Loop
// ========


    // e.g. for i in range(10): ...
    rule #compileStmt(%forrange(NAME, ROUNDS, STMTS))
        => #forrange(#newLoopVar(NAME), @tlll(%num, 0, @none), ROUNDS, #compileStmts(STMTS, .LLLExps))

    // e.g. for i in range(100, 110): ...
    rule #compileStmt(%forrange(NAME, START:Int, END:Int, STMTS))
        => #forrange(#newLoopVar(NAME), @tlll(%num, START, @none), END -Int START, #compileStmts(STMTS, .LLLExps))

    // e.g. for i in range(x, x + 10): ...
    rule #compileStmt(%forrange(NAME, %var(V), %binop(+, %var(V), ROUNDS:Int), STMTS))
        => #forrange(#newLoopVar(NAME), #compileValueExpr(%var(V)), ROUNDS, #compileStmts(STMTS, .LLLExps))

    //TODO: e.g. for i in list(): ...


    syntax CLLLExps  ::= "#forrange" "(" CTypedLLLExp           ","
                                         CTypedLLLExp /*start*/ ","
                                         Int         /*rounds*/ ","
                                         CLLLExps
                                     ")"         [seqstrict(1,2,4)]
 // ---------------------------------------------------------------
    rule #forrange(@tlll(%num, LOC:Int, _), @tlll(_, STARTCODE, _), ROUNDS, BODYCODE:LLLExps)
        => $repeat(LOC, STARTCODE, ROUNDS, $%seq(BODYCODE)),.LLLExps


// Break
// =====


    rule #compileStmt(%break) => $break,.LLLExps


// Pass
// =====


    rule #compileStmt(%pass)  => $pass,.LLLExps


// Return
// ======


    rule <k> #compileStmt(%return) => #ifThenElse(T =/=K %void,
                                                  #exception("Expecting to return a value"),
                                                  $return(0, 0)) ... </k>
         <return> T </return>

    rule <k> #compileStmt(%return(E)) => #ifThenElse(T =/=K %void,
                                                     #return(#compileExpr(E), T),
                                                     #exception("Not expecting to return a value")) ... </k>
         <return> T </return>


    syntax CLLLExps  ::= "#return" "(" CTypedLLLExp "," Type /*return type*/ ")"  [strict(1)]
 // -----------------------------------------------------------------------------------------
    rule #return(@tlll(T, CODE, EXPRATTR), RETURNTYPE)
        => #ifThen(notBool(isBaseType(RETURNTYPE)),
                   #exception("Trying to return base type but output expecting non base type."))
        ~> #returnBase(#unwrapLoc(@tlll(T, CODE, EXPRATTR)), RETURNTYPE)
      requires isBaseType(T)

    // TODO: support byte array

    rule #return(@tlll(T, CODE, EXPRATTR), RETURNTYPE)
        => #ifThenElse(#isInMemory(EXPRATTR) andBool (notBool(isMultiLLLExp(CODE))),
                       $return(CODE, #sizeOfType(RETURNTYPE)),
                       #returnListT(#newPlaceholder(RETURNTYPE),
                                    @tlll(T, CODE, EXPRATTR),
                                    RETURNTYPE))
      requires isListType(T)


    syntax CLLLExps  ::= "#returnBase" "(" TypedLLLExp "," Type ")"
 // ---------------------------------------------------------------
    rule #returnBase(@tlll(T, CODE, _), RETURNTYPE)
             => #ifThenElse((T ==K RETURNTYPE) orBool (T ==K %num andBool RETURNTYPE ==K %signed256),
                            $%seq($mstore(0, CODE), $return(0, 32),.LLLExps),.LLLExps,
                            #exception("Unsupported type conversion."))


    syntax CLLLExps  ::= "#returnListT"    "(" CTypedLLLExp ","  // place holder
                                               TypedLLLExp  ","
                                               Type
                                           ")"      [strict(1)]

    syntax CLLLExps  ::= "#returnListTAux" "(" CLLLExps     ","
                                               Int          ","
                                               Type
                                           ")"      [strict(1)]
 // --------------------------------------------------------------------------
    rule #returnListT(@tlll(T, LOC, LOCATTR), TCODE, RETURNTYPE)
        => #returnListTAux(#mkSetter(@tlll(T, LOC, LOCATTR), TCODE),
                           LOC, RETURNTYPE)

    rule #returnListTAux(SETTER, LOC, RETURNTYPE)
        => $%seq(SETTER ++LLL ($return(LOC, #sizeOfType(RETURNTYPE)),.LLLExps)),.LLLExps


// Assert
// ======


    rule #compileStmt(%assert(EXPR)) => #assert(#compileValueExpr(EXPR))


    syntax CLLLExps  ::= "#assert" "(" CTypedLLLExp ")"  [strict]
 // -------------------------------------------------------------
    rule #assert(@tlll(_, CODE, _)) => $assert(CODE)


// Throw
// =====


    rule #compileStmt(%throw) => $assert(0),.LLLExps


// Send
// ====

    rule <k> #compileStmt(%send(TO, VALUE))
                 => #ifThenElse(CONSTANT ==K false,
                                #send(#compileValueExpr(TO), #compileValueExpr(VALUE)),
                                #exception("Cannot send ether inside a constant function")) ... </k>
         <constant> CONSTANT </constant>


    syntax CLLLExps  ::= "#send" "(" CTypedLLLExp /*to*/ "," CTypedLLLExp /*value*/ ")"  [seqstrict]
 // ------------------------------------------------------------------------------------------------
    rule #send(@tlll(%address, TOCODE, _), @tlll(%unitT(%num, %wei, _), VALUECODE, _))
             => $assert($call(0, TOCODE, VALUECODE, 0, 0, 0, 0)),.LLLExps


// Log
// ====


    rule <k> #compileStmt(%log(NAME, ARGS)) => #log(ARGS, EVENTRECORD) ... </k>
         <internalSig> NAME |-> EVENTRECORD:EventRecord SIGS </internalSig>

    rule <k> #compileStmt(%log(NAME, _))
            => #exception("Event not declared yet: " +String Id2String(NAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool NAME in keys(SIGS)


    syntax CLLLExps  ::= "#log"    "(" Exprs "," EventRecord ")"

    syntax CLLLExps  ::= "#logAux" "(" Int         ","  // event id
                                       Exprs       ","
                                       EventParams ","
                                       Exprs       ","  // topic args
                                       EventParams ","  // topic params
                                       Exprs       ","  // data args
                                       EventParams ")"  // data params
 // --------------------------------------------------
    rule #log(ARGS, @event(EID, ENAME, EPARAMS))
        => #ifThenElse(#numOfExprs(ARGS) =/=K #numOfEventParams(EPARAMS),
                       #exception("# of args doesn't match # of params in event " +String
                                  Id2String(ENAME) +String
                                  " expected: " +String Int2String(#numOfEventParams(EPARAMS)) +String
                                  ", actual: " +String Int2String(#numOfExprs(ARGS))),
                       #logAux(EID, ARGS, EPARAMS, .Exprs, .EventParams, .Exprs, .EventParams))

    rule #logAux(EID, (ARG1 ARGS), (EPARAM1 EPARAMS), TARGS, TEPARAMS, DARGS, DEPARAMS)
        => #ifThenElse(#isTopic(EPARAM1),
                       #logAux(EID, ARGS, EPARAMS, TARGS ++Expr ARG1, TEPARAMS ++Eparam EPARAM1, DARGS, DEPARAMS),
                       #logAux(EID, ARGS, EPARAMS, TARGS, TEPARAMS, DARGS ++Expr ARG1, DEPARAMS ++Eparam EPARAM1))

    // 0 topic
    rule #logAux(EID, .Exprs, .EventParams, .Exprs, .EventParams, DARGS, DEPARAMS)
        => #log1(EID, #packLoggingData(DARGS, DEPARAMS))

    // 1 topic
    rule #logAux(EID, .Exprs, .EventParams, (TARG1 .Exprs), (TEPARAM1 .EventParams), DARGS, DEPARAMS)
        => #log2(EID,
                 #packLoggingTopic(#compileExpr(TARG1), TEPARAM1),
                 #packLoggingData(DARGS, DEPARAMS))

    // 2 topics
    rule #logAux(EID, .Exprs, .EventParams, (TARG1 TARG2 .Exprs), (TEPARAM1 TEPARAM2 .EventParams), DARGS, DEPARAMS)
        => #log3(EID,
                 #packLoggingTopic(#compileExpr(TARG1), TEPARAM1),
                 #packLoggingTopic(#compileExpr(TARG2), TEPARAM2),
                 #packLoggingData(DARGS, DEPARAMS))

    // 3 topics
    rule #logAux(EID, .Exprs, .EventParams, (TARG1 TARG2 TARG3 .Exprs), (TEPARAM1 TEPARAM2 TEPARAM3 .EventParams), DARGS, DEPARAMS)
        => #log4(EID,
                 #packLoggingTopic(#compileExpr(TARG1), TEPARAM1),
                 #packLoggingTopic(#compileExpr(TARG2), TEPARAM2),
                 #packLoggintTopic(#compileExpr(TARG3), TEPARAM3),
                 #packLoggingData(DARGS, DEPARAMS))


    syntax CLLLExps ::= "#log1" "(" Int                ","
                                    CPackedLoggingData
                                ")"            [strict(2)]

    syntax CLLLExps ::= "#log2" "(" Int                ","
                                    CTypedLLLExp       ","
                                    CPackedLoggingData
                                ")"       [seqstrict(2,3)]

    syntax CLLLExps ::= "#log3" "(" Int                ","
                                    CTypedLLLExp       ","
                                    CTypedLLLExp       ","
                                    CPackedLoggingData
                                ")"     [seqstrict(2,3,4)]

    syntax CLLLExps ::= "#log4" "(" Int                ","
                                    CTypedLLLExp       ","
                                    CTypedLLLExp       ","
                                    CTypedLLLExp       ","
                                    CPackedLoggingData
                                ")"   [seqstrict(2,3,4,5)]
 // ------------------------------------------------------
    rule #log1(EID, @loggingdata(DATACODE, START, SIZE))
        => $%seq(
             DATACODE,
             $log1(START, SIZE, EID),.LLLExps),.LLLExps

    rule #log2(EID, @tlll(_, TOPIC1, _), @loggingdata(DATACODE, START, SIZE))
        => $%seq(
             DATACODE,
             $log2(START, SIZE, EID, TOPIC1),.LLLExps),.LLLExps

    rule #log3(EID, @tlll(_, TOPIC1, _), @tlll(_, TOPIC2, _), @loggingdata(DATACODE, START, SIZE))
        => $%seq(
             DATACODE,
             $log3(START, SIZE, EID, TOPIC1, TOPIC2),.LLLExps),.LLLExps

    rule #log4(EID, @tlll(_, TOPIC1, _), @tlll(_, TOPIC2, _), @tlll(_, TOPIC3, _), @loggingdata(DATACODE, START, SIZE))
        => $%seq(
             DATACODE,
             $log4(START, SIZE, EID, TOPIC1, TOPIC2, TOPIC3),.LLLExps),.LLLExps


    syntax CPackedLoggingData  ::= "#packLoggingData"    "(" Exprs        ","
                                                             EventParams  ")"

    syntax CPackedLoggingData  ::= "#packLoggingDataAux" "(" Exprs        ","
                                                             EventParams  ","
                                                             LLLExps      ","
                                                             Int          ")"  // size of the packed data
 // -------------------------------------------------------------------------
    rule #packLoggingData(DARGS, DEPARAMS)
        => #ifThenElse(#numOfExprs(DARGS) ==Int 0,
                       @loggingdata($pass, 0, 0),
                       #packLoggingDataAux(DARGS, DEPARAMS, .LLLExps, 0))

    rule #packLoggingDataAux(.Exprs, .EventParams, CODE, SIZE)
        => @loggingdata($%seq(CODE), #getFirstStoreLoc(CODE), SIZE)

    rule #packLoggingDataAux((DARG DARGS), %eparam(_, T, _) DEPARAMS, CODE, SIZE)
        => #packArgBy32(#newPlaceholder(T), DARG, T)
        ~> #packLoggingDataAux(DARGS, DEPARAMS, CODE, SIZE)

    rule @argby32(ARGCODE, ARGSIZE) ~> #packLoggingDataAux(DARGS, DEPARAMS, CODE, TOTALSIZE)
        => #packLoggingDataAux(DARGS, DEPARAMS, CODE ++LLL ARGCODE, TOTALSIZE +Int ARGSIZE)


    syntax CPackedArgBy32  ::= "#packArgBy32" "(" CTypedLLLExp ","  // start loc
                                                  Expr         ","  // value
                                                  Type
                                              ")"      [strict(1)]
 // --------------------------------------------------------------
    rule #packArgBy32(PLACEHOLDER, EXPR, T)
        => #packArgBy32Base(PLACEHOLDER, #compileExpr(EXPR), T)
      requires isBaseType(T)

    // TODO: Add support for ByteArray

    // TODO: Add support for List


    syntax CPackedArgBy32  ::= "#packArgBy32Base"    "(" TypedLLLExp  ","
                                                         CTypedLLLExp ","
                                                         Type         ")"  [strict(2)]

    syntax CPackedArgBy32  ::= "#packArgBy32BaseAux" "(" Int          ","
                                                         CTypedLLLExp ")"  [strict(2)]
 // ----------------------------------------------------------------------------------
    rule #packArgBy32Base(@tlll(_, LOC:Int, _), TCODE, ARGTYPE)
        => #packArgBy32BaseAux(LOC, #baseTypeConvert(TCODE, ARGTYPE))

    rule #packArgBy32BaseAux(LOC, @tlll(_, CODE, _)) => @argby32($mstore(LOC, CODE),.LLLExps, 32)


    syntax CTypedLLLExp  ::= "#packLoggingTopic" "(" CTypedLLLExp "," EventParams ")"  [strict(1)]
 // ----------------------------------------------------------------------------------------------
    rule #packLoggingTopic(ARGCODE, %eparam(_, T, _)) => #baseTypeConvert(ARGCODE, T)
      requires isBaseType(T)


///////////////////////////////////////////////////////////////////////////////
// Expressions
///////////////////////////////////////////////////////////////////////////////


    // Compile an expression that results in a value
    syntax CTypedLLLExp  ::= "#compileValueExpr"    "(" Expr ")"
    syntax CTypedLLLExp  ::= "#compileValueExprAux" "(" CTypedLLLExp ")"  [strict]
 // ------------------------------------------------------------------------------
    rule #compileValueExpr(EXPR) => #compileValueExprAux(#compileExpr(EXPR))

    rule #compileValueExprAux(TCODE) => #unwrapLoc(TCODE)




    // Compile an expression that represents an address in memory or storage
    syntax CTypedLLLExp  ::= "#compileLocExpr"    "(" Expr ")"
    syntax CTypedLLLExp  ::= "#compileLocExprAux" "(" CTypedLLLExp ")"  [strict]
 // ---------------------------------------------------------------------------
    rule #compileLocExpr(EXPR) => #compileLocExprAux(#compileExpr(EXPR))

    rule #compileLocExprAux(@tlll(T, CODE, EXPRATTR))
        => #ifThenElse(EXPRATTR ==K @none,
                       #exception("Looking for a variable location, instead got a value"),
                       @tlll(T, CODE, EXPRATTR))


    syntax CTypedLLLExp  ::= "#compileExpr" "(" Expr ")"
 // ----------------------------------------------------


// Number
// ======


    rule #compileExpr(NUM:Int) => #ifThenElse((NUM >=Int @minNum) andBool (NUM <=Int @maxNum),
                                              @tlll(%num, NUM, @none),
                                              #exception("Number out of range"))

    rule #compileExpr(%fixed10(NUM, DEN))
        => #ifThen(notBool((NUM >=Int (@minNum *Int DEN)) andBool (NUM >=Int (@minNum *Int DEN))),
                   #exception("Number out of range."))
        ~> #ifThen(@decimalDivisor <Int DEN,
                   #exception("Too many decimal places."))
        ~> @tlll(%decimal, (NUM *Int @decimalDivisor) /Int DEN, @none)

    rule #compileExpr(%hex(STR))
        => #ifThenElse(lengthString(STR) ==Int 40,
                       @tlll(%address, String2Base(STR, 16), @none),
             #ifThenElse(lengthString(STR) ==Int 64,
                         @tlll(%bytes32, String2Base(STR, 16), @none),
                         #exception("Cannot read 0x value with length:" +String Int2String(lengthString(STR)))))


// Bool
// ====


    rule #compileExpr(true)  => @tlll(%bool, 1, @none)

    rule #compileExpr(false)  => @tlll(%bool, 0, @none)


// Variable
// ========


    rule #compileExpr(%self) => @tlll(%address, $address, @none)

    rule #compileExpr(V) => #lookupVar(V)


// List
// ====


    rule #compileExpr(%list(EXPRS)) => #listLiterals(EXPRS)
      requires #numOfExprs(EXPRS) >Int 0

    rule #compileExpr(%list(EXPRS)) => #exception("List must have elements")
      requires #numOfExprs(EXPRS) ==Int 0


    // Additional LLLExp to handle lists
    syntax MultiLLLExp  ::= "$multi" "(" TypedLLLExps ")"
    syntax LLLExp       ::= MultiLLLExp
 // ------------------------------------------------


    syntax CTypedLLLExp  ::= "#listLiterals" "(" Exprs ")"
 // ------------------------------------------------------
    rule #listLiterals(EXPR EXPRS) => #processListLiteralsFirstElem(EXPR)
                                   ~> #processListLiteralsRestElems(EXPRS, .TypedLLLExps)


    syntax CTypedLLLExp  ::= "#processListLiteralsFirstElem" "(" Expr ")"
 // ----------------------------------------------------------------------
    rule #processListLiteralsFirstElem(EXPR) => #compileExpr(EXPR)


    syntax CTypedLLLExp  ::= "#processListLiteralsRestElems"    "(" Exprs "," TypedLLLExps ")"
    syntax CTypedLLLExp  ::= "#processListLiteralsRestElemsAux" "(" Type "," Int "," Exprs "," TypedLLLExps ")"
 // -----------------------------------------------------------------------------------------------------------
    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralsRestElems(EXPRS, .TypedLLLExps)
        => #processListLiteralsRestElemsAux(T, 1, EXPRS, @tlll(T, CODE, EXPRATTR) .TypedLLLExps)

    rule #processListLiteralsRestElemsAux(T, LEN, .Exprs, RESULTCODE)
        => @tlll(%listT(T, LEN), $multi(RESULTCODE), @none)

    rule #processListLiteralsRestElemsAux(T, LEN, (EXPR EXPRS), RESULTCODE)
        => #compileExpr(EXPR) ~> #processListLiteralsRestElemsAux(T, LEN, EXPRS, RESULTCODE)

    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralsRestElemsAux(T, LEN, EXPRS, RESULTCODE)
        => #processListLiteralsRestElemsAux(T, LEN +Int 1, EXPRS,
                                            RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))

    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralsRestElemsAux(ELEMT, LEN, EXPRS, RESULTCODE)
        => #processListLiteralsRestElemsAux(%mixedT, LEN +Int 1, EXPRS,
                                            RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))
      requires T =/=K ELEMT


// Arithmetic
// ==========


    rule #compileExpr(%binop(BOP, LEXPR, REXPR))
        => #binOp(BOP, #compileValueExpr(LEXPR), #compileValueExpr(REXPR))


    syntax CTypedLLLExp  ::= "#binOp" "(" BinOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
 // ---------------------------------------------------------------------------------------------------
    // TODO: support unit type

    rule #binOp(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
             => #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
                        #exception("Unsupported types for arithmetic op"))
             ~> #ifThenElse(isPureNumType(LT) andBool isPureNumType(RT),
                            #binOpPure(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR)),
                            #exception("Do not support unit type yet."))
             ~> #clampArithResult


    syntax CTypedLLLExp  ::= "#binOpPure" "(" BinOp "," TypedLLLExp  "," TypedLLLExp  ")"
 // -------------------------------------------------------------------------------------
    rule #binOpPure(+, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $add(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                         @tlll(%decimal, $add($mul(LCODE, @decimalDivisor), RCODE), @none),
               #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                           @tlll(%decimal, $add(LCODE, $mul(RCODE, @decimalDivisor)), @none),
                           #exception("How did I get here?"))))

    rule #binOpPure(-, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $sub(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                         @tlll(%decimal, $sub($mul(LCODE, @decimalDivisor), RCODE), @none),
               #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                           @tlll(%decimal, $sub(LCODE, $mul(RCODE, @decimalDivisor)), @none),
                           #exception("How did I get here?"))))

    rule #binOpPure(*, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT andBool LT ==K %num,
                       @tlll(%num, $mul(LCODE, RCODE), @none),
             #ifThenElse(LT ==K RT andBool LT ==K %decimal,
                         @tlll(%decimal, $with($_r, RCODE,
                                           $with($_l, LCODE,
                                             $with($_ans, $mul($_l, $_r),
                                               $%seq(
                                                 $assert($or($eq($sdiv($_ans, $_l), $_r), $not($_l))),
                                                 $sdiv($_ans, @decimalDivisor),.LLLExps)))), @none),
               #ifThen((LT ==K %num andBool RT ==K %decimal) orBool (LT ==K %decimal andBool RT ==K %num),
                       @tlll(%decimal, $with($_r, RCODE,
                                         $with($_l, LCODE,
                                           $with($_ans, $mul($_l, $_r),
                                             $%seq(
                                               $assert($or($eq($sdiv($_ans, $_l), $_r), $not($_l))),
                                               $_ans,.LLLExps)))), @none))))

    rule #binOpPure(/, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(RT ==K %num,
                       @tlll(LT, $sdiv(LCODE, $clamp_nonzero(RCODE)), @none),
             #ifThenElse(LT ==K RT andBool LT ==K %decimal,
                         @tlll(%decimal, $with($_l, LCODE,
                                           $with($_r, $clamp_nonzero(RCODE),
                                             $sdiv($mul($_l, @decimalDivisor), $_r))), @none),
               #ifThen(LT ==K %num andBool RT ==K %decimal,
                       @tlll(%decimal,
                             $sdiv($mul(LCODE, @decimalDivisor ^Int 2), $clamp_nonzero(RCODE)), @none))))

    rule #binOpPure(%, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $smod(LCODE, $clamp_nonzero(RCODE)), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%decimal, $smod(LCODE, $mul($clamp_nonzero(RCODE), @decimalDivisor)), @none),
               #ifThen(LT ==K %num andBool RT ==K %decimal,
                       @tlll(%decimal, $smod($mul(LCODE, @decimalDivisor), $clamp_nonzero(RCODE)), @none))))

    rule #binOpPure(**, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT andBool LT ==K %num,
                       @tlll(%num, $exp(LCODE, RCODE), @none),
                       #exception("Only whole number exponents are supported"))


    syntax KItem  ::= "#clampArithResult"
 // -------------------------------------
    rule @tlll(%num, CODE, _) ~> #clampArithResult
        => @tlll(%num, $clamp($mload(@minNumPos), CODE, $mload(@maxNumPos)), @none)

    rule @tlll(%decimal, CODE, _) ~> #clampArithResult
        => @tlll(%decimal, $clamp($mload(@minDecimalPos), CODE, $mload(@maxDecimalPos)), @none)


// Compare
// =======


    rule #compileExpr(%compareop(COP, LEXP, REXP))
        => #compareOp(COP, #compileValueExpr(LEXP), #compileValueExpr(REXP))


    syntax CTypedLLLExp  ::= "#compareOp"    "(" CompareOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp  ::= "#compareOpAux" "(" CompareOp "," TypedLLLExp  "," TypedLLLExp ")"
 // --------------------------------------------------------------------------------------------------------------
    //TODO: support `in` operator

    rule #compareOp(COP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
             #ifThen(COP =/=K %eq andBool COP =/=K %ne,
                     #exception("Invalid type for comparison op")))
           ~> #compareOpAux(COP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))

    rule #compareOpAux(%gt, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(%bool, $sgt(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%bool, $sgt(LCODE, $mul(RCODE, @decimalDivisor)), @none),
               #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                           @tlll(%bool, $sgt($mul(LCODE, @decimalDivisor), RCODE), @none),
                           #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%ge, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(%bool, $sge(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%bool, $sge(LCODE, $mul(RCODE, @decimalDivisor)), @none),
               #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                           @tlll(%bool, $sge($mul(LCODE, @decimalDivisor), RCODE), @none),
                           #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%lt, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(%bool, $slt(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%bool, $slt(LCODE, $mul(RCODE, @decimalDivisor)), @none),
               #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                           @tlll(%bool, $slt($mul(LCODE, @decimalDivisor), RCODE), @none),
                           #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%le, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(%bool, $sle(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%bool, $sle(LCODE, $mul(RCODE, @decimalDivisor)), @none),
               #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                           @tlll(%bool, $sle($mul(LCODE, @decimalDivisor), RCODE), @none),
                           #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%eq, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(%bool, $eq(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%bool, $eq(LCODE, $mul(RCODE, @decimalDivisor)), @none),
               #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                           @tlll(%bool, $eq($mul(LCODE, @decimalDivisor), RCODE), @none),
                           #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%ne, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(%bool, $ne(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%bool, $ne(LCODE, $mul(RCODE, @decimalDivisor)), @none),
               #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                           @tlll(%bool, $ne($mul(LCODE, @decimalDivisor), RCODE), @none),
                           #exception("Unsupported types for comparison"))))


// Boolean Operation
// =================


    rule #compileExpr(%boolop(BOP, LEXP, REXP)) => #boolOp(BOP, #compileValueExpr(LEXP), #compileExpr(REXP))


    syntax CTypedLLLExp  ::= "#boolOp" "(" BoolOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp  ::= "#boolOpAux" "(" BoolOp "," TypedLLLExp "," TypedLLLExp ")"
 // ----------------------------------------------------------------------------------------------------
    rule #boolOp(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThenElse((LT ==K %bool) andBool (RT ==K %bool),
                        #boolOpAux(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR)),
                        #exception("Boolean operations can only be between booleans!"))

    rule #boolOpAux(%and, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => @tlll(%bool, $and(LCODE, RCODE), @none)

    rule #boolOpAux(%or, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => @tlll(%bool, $or(LCODE, RCODE), @none)


// Unary Operation
// ===============


    rule #compileExpr(%unaryop(UOP, EXPR)) => #unaryOp(UOP, #compileValueExpr(EXPR))


    syntax CTypedLLLExp  ::= "#unaryOp" "(" UnaryOp "," CTypedLLLExp ")"    [strict(2)]
 // -----------------------------------------------------------------------------------
    rule #unaryOp(%not, @tlll(T, CODE, _)) => @tlll(%bool, $iszero(CODE), @none)

    rule #unaryOp(%neg, @tlll(T, CODE, _)) => #ifThenElse(isNumericType(T),
                                                          @tlll(T, $sub(0, CODE), @none),
                                                          #exception("Unsupported type for negation."))



// Internal Contract Call
// ======================


    syntax CTypedLLLExp  ::= "#icall"    "(" Exprs "," FuncRecord ")"

    syntax CTypedLLLExp  ::= "#icallAux" "(" CPackedArgData                ","
                                             CTypedLLLExp /*return start*/ ","
                                             Int          /*return width*/
                                         ")"                       [seqstrict]
 // --------------------------------------------------------------------------
    rule <k> #compileExpr(%icall(FNAME, ARGS)) => #icall(ARGS, FUNCRECORD) ... </k>
         <internalSig> FNAME |-> FUNCRECORD SIGS </internalSig>

    // TODO: Is it necessary to enforce that functions cannot call functions defined later than themselves?
    rule <k> #compileExpr(%icall(FNAME, _)) => #exception("Function not declared yet: " +String Id2String(FNAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool FNAME in keys(SIGS)

    // EVM: CALL GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
    rule <k> #icall(ARGS, @func(FUNCID, FNAME, PARAMS, T, _, _, _))
            => #ifThen(#numOfExprs(ARGS) =/=K #numOfParams(PARAMS),
                       #exception("# of args doesn't match # of params in function" +String Id2String(FNAME) +String
                                  " expected: " +String Int2String(#numOfParams(PARAMS)) +String
                                  ", actual: " +String Int2String(#numOfExprs(ARGS))))
            ~> #icallAux(#packArguments(#newPlaceholder(%bytesT(#sizeOfParams(PARAMS) +Int 32)), FUNCID, ARGS, PARAMS),
                         #newPlaceholder(T),
                         #sizeOfType(T))
         ... </k>

    rule #icallAux(@argdata(CODE, ARGSWIDTH), @tlll(RETT, LOC, _), RETWIDTH)
        => @tlll(RETT, $%seq(
                         $assert($call($gas, $address, 0, CODE, ARGSWIDTH, LOC, RETWIDTH)),
                         LOC,.LLLExps
                       ), @locattr(@memory, true))
      requires isBaseType(RETT)


    syntax CPackedArgData  ::= "#packArguments"    "(" CTypedLLLExp      ","
                                                       Int   /*func id*/ ","
                                                       Exprs             ","
                                                       Params
                                                   ")"           [strict(1)]

    syntax CPackedArgData  ::= "#packArgumentsAux" "(" Int   /*arg loc*/ ","
                                                       Exprs             ","
                                                       Params            ","
                                                       LLLExps           ","
                                                       Int /*arg start*/ ","
                                                       Int /*arg width*/ ","
                                                       Bool /*need pos?*/")"
 // ------------------------------------------------------------------------
    rule #packArguments(@tlll(T, LOC, _), FUNCID, ARGS, PARAMS)
        => #packArgumentsAux(LOC +Int 32, ARGS, PARAMS, $mstore(LOC, FUNCID),.LLLExps,
                             LOC +Int 28, #sizeOfParams(PARAMS) +Int 4, false)

    rule #packArgumentsAux(_, .Exprs, .Params, RESULTCODE, ARGSSTART, ARGSWIDTH, false)
        => @argdata($%seq(RESULTCODE ++LLL (ARGSSTART,.LLLExps)), ARGSWIDTH)

    rule #packArgumentsAux(ARGLOC, (ARG ARGS), (%param(_, T) PARAMS), RESULTCODE, ARGSSTART, ARGSWIDTH, NEEDPOS)
        => #packArgumentBase(@tlll(T, ARGLOC, @locattr(@memory, true)), #compileExpr(ARG))
        ~> #packArgumentsAux(ARGLOC, ARGS, PARAMS, RESULTCODE, ARGSSTART, ARGSWIDTH, NEEDPOS)
      requires isBaseType(T)

    rule CODE:LLLExps ~> #packArgumentsAux(ARGLOC, ARGS, PARAMS, RESULTCODE, ARGSSTART, ARGSWIDTH, NEEDPOS)
        => #packArgumentsAux(ARGLOC +Int 32, ARGS, PARAMS, RESULTCODE ++LLL CODE, ARGSSTART, ARGSWIDTH, NEEDPOS)


    syntax CLLLExps  ::= "#packArgumentBase" "(" TypedLLLExp       ","
                                                 CTypedLLLExp
                                             ")"           [strict(2)]
 // -------------------------------------------------------------- ---

    rule #packArgumentBase(@tlll(PARAMT, LOC, LOCATTR), TCODE)
        => #mkSetter(@tlll(PARAMT, LOC, LOCATTR), TCODE)


    // Reserved Expr
    rule #compileExpr(%msg.sender)       => @tlll(%address, $caller, @none)

    rule #compileExpr(%msg.value)        => @tlll(%unitT(%num, %wei, false), $callvalue, @none)

    rule #compileExpr(%msg.gas)          => @tlll(%num, $gas, @none)

    rule #compileExpr(%block.difficulty) => @tlll(%num, $difficulty, @none)

    rule #compileExpr(%block.timestamp)  => @tlll(%unitT(%num, %sec, true), $timestamp, @none)

    rule #compileExpr(%block.coinbase)   => @tlll(%address, $coinbase, @none)

    rule #compileExpr(%block.number)     => @tlll(%num, $number, @none)

    rule #compileExpr(%block.prevhash)   => @tlll(%bytes32, $blockhash($sub($number, 1)), @none)

    rule #compileExpr(%tx.origin)        => @tlll(%address, $origin, @none)


    // Reserved Func
    rule #compileExpr(%as_num128(EXPR)) => #asNum128(#compileValueExpr(EXPR))

    rule #compileExpr(%as_num256(EXPR)) => #asNum256(#compileValueExpr(EXPR))

    rule #compileExpr(%as_wei_value(EXPR, UNIT)) => #asWeiValue(#compileValueExpr(EXPR), UNIT)

    rule #compileExpr(%num256_add(LEFTE, RIGHTE)) => #num256Add(#compileValueExpr(LEFTE), #compileValueExpr(RIGHTE))

    rule #compileExpr(%num256_sub(LEFTE, RIGHTE)) => #num256Sub(#compileValueExpr(LEFTE), #compileValueExpr(RIGHTE))


    syntax CTypedLLLExp ::= "#asNum128"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp ::= "#asNum128Aux" "(" LLLExp ")"
 // -----------------------------------------------------------------------
    rule #asNum128(@tlll(T, CODE, _))
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %num256) orBool #isTypeOf(T, %address),
                            #asNum128Aux(CODE),
                            #exception("Function arg type does not match expected type."))

    rule #asNum128Aux(CODE) => @tlll(%num, $clamp($mload(@minNumPos), CODE, $mload(@maxNumPos)), @none)


    syntax CTypedLLLExp ::= "#asNum256"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp ::= "#asNum256Aux" "(" TypedLLLExp ")"
    syntax CTypedLLLExp ::= "#asNum256ForNumber" "(" LLLExp ")"
    syntax CTypedLLLExp ::= "#asNum256ForLLLExp" "(" LLLExp ")"
 // -----------------------------------------------------------------------
    rule #asNum256(@tlll(T, CODE, EXPRATTR))
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %address),
                            #asNum256Aux(@tlll(T, CODE, EXPRATTR)),
                            #exception("Function arg type does not match expected type."))

    rule #asNum256Aux(@tlll(T, CODE, EXPRATTR)) => #ifThenElse(isInt(CODE),
                                                               #asNum256ForNumber(CODE),
                                                               #asNum256ForLLLExp(CODE))

    rule #asNum256ForNumber(I:Int) => #ifThenElse((I >=Int 0) andBool (I <=Int 2^Int 256 -Int 1),
                                                   @tlll(%num256, I, @none),
                                                   #exception("Number out of range"))

    rule #asNum256ForLLLExp(CODE) => @tlll(%num256, CODE, @none)


    syntax CTypedLLLExp ::= "#asWeiValue"    "(" CTypedLLLExp "," Id  ")"                [strict(1)]
    syntax CTypedLLLExp ::= "#asWeiValueAux" "(" TypedLLLExp  "," Int ")"
    syntax CTypedLLLExp ::= "#asWeiValueForNumber" "(" LLLExp      "," Int ")"
    syntax CTypedLLLExp ::= "#asWeiValueForLLLExp" "(" TypedLLLExp "," Int ")"
 // ------------------------------------------------------------------------------------------------
    rule #asWeiValue(@tlll(T, CODE, EXPRATTR), UNIT)
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %decimal),
                            #asWeiValueAux(@tlll(T, CODE, EXPRATTR), #convertToWei(UNIT)),
                            #exception("Function arg type does not match expected type."))

    rule #asWeiValueAux(@tlll(T, CODE, EXPRATTR), DENOMINATION)
             => #ifThenElse(isInt(CODE),
                            #asWeiValueForNumber(CODE, DENOMINATION),
                            #asWeiValueForLLLExp(@tlll(T, CODE, EXPRATTR), DENOMINATION))

    rule #asWeiValueForLLLExp(@tlll(%num, CODE, EXPRATTR), DENOMINATION)
        => @tlll(%unitT(%num, %wei, false), $mul(CODE, DENOMINATION), @none)

    rule #asWeiValueForLLLExp(@tlll(%decimal, CODE, EXPRATTR), DENOMINATION)
             => @tlll(%unitT(%num, %wei, false), $div($mul(CODE, DENOMINATION), @decimalDivisor), @none)


    syntax CTypedLLLExp ::= "#num256Add"    "(" CTypedLLLExp "," CTypedLLLExp ")"        [seqstrict]
    syntax CTypedLLLExp ::= "#num256AddAux" "(" LLLExp "," LLLExp ")"
 // ------------------------------------------------------------------------------------------------
    rule #num256Add(@tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
            => #ifThenElse(#isTypeOf(LT, %num256) andBool #isTypeOf(RT, %num256),
                           #num256AddAux(LCODE, RCODE),
                           #exception("Function arg type does not match expected type."))

    rule #num256AddAux(LCODE, RCODE)
             => @tlll(%num256, $%seq(
                                 $assert($or($iszero(RCODE), $gt($add(LCODE, RCODE), LCODE))),
                                 $add(LCODE, RCODE),.LLLExps), @none)


    syntax CTypedLLLExp ::= "#num256Sub"    "(" CTypedLLLExp "," CTypedLLLExp ")"        [seqstrict]
    syntax CTypedLLLExp ::= "#num256SubAux" "(" LLLExp "," LLLExp ")"
 // ------------------------------------------------------------------------------------------------
    rule #num256Sub(@tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
            => #ifThenElse(#isTypeOf(LT, %num256) andBool #isTypeOf(RT, %num256),
                           #num256SubAux(LCODE, RCODE),
                           #exception("Function arg type does not match expected type."))

    rule #num256SubAux(LCODE, RCODE)
             => @tlll(%num256, $%seq(
                                 $assert($ge(LCODE, RCODE)),
                                 $sub(LCODE, RCODE),.LLLExps), @none)


//////////////////////////////////////////////////////////////////////////////
// Utils
//////////////////////////////////////////////////////////////////////////////


    syntax Bool  ::= "#isInitFunc" "(" Id ")"    [function]
 // -------------------------------------------------------
    rule #isInitFunc(FNAME) => FNAME ==K __init__


    syntax Bool  ::= "#isTypeOf" "(" Type "," Type /*target type*/ ")"    [function]
 // --------------------------------------------------------------------------------
    rule #isTypeOf(T, TARGET) => #isUnitTypeOf(T, TARGET)
      requires isUnitType(T)

    rule #isTypeOf(T, TARGET) => T ==K TARGET
      requires notBool isUnitType(T)


    syntax Bool  ::= "#isUnitTypeOf" "(" UnitType "," Type ")"    [function]
 // ------------------------------------------------------------------------
    rule #isUnitTypeOf(%unitT(T, _, _), T) => true

    rule #isUnitTypeOf(%unitT(T, _, _), TARGET) => false
      requires T =/=K TARGET


    syntax Bool  ::= "#isTopic" "(" EventParam ")"    [function]
 // ------------------------------------------------------------
    rule #isTopic(%eparam(_, _, ISTOPIC)) => ISTOPIC


    syntax Bool  ::= "#isInMemory" "(" LLLExpAttr ")"   [function]
 // --------------------------------------------------------------
    rule #isInMemory(@locattr(@memory, _)) => true

    rule #isInMemory(@locattr(@storage, _)) => false

    rule #isInMemory(@locattr(@storage_prehashed, _)) => false

    rule #isInMemory(@none) => false


// Exception
// ======================

    syntax KItem  ::= "#exception" "(" String ")"
 // ---------------------------------------------



// List Concatenation
// ==================


    syntax Defs  ::= Defs "++Def" Defs    [right, function]
 // -------------------------------------------------------
    rule .Defs ++Def DEFS:Defs => DEFS

    rule (DEF DEFS1) ++Def DEFS2:Defs => DEF (DEFS1 ++Def DEFS2)


    syntax Params  ::= Params "++Param" Params    [right, function]
 // ---------------------------------------------------------------
    rule .Params ++Param PARAMS:Params => PARAMS

    rule (PARAM PARAMS1) ++Param PARAMS2 => PARAM (PARAMS1 ++Param PARAMS2)


    syntax EventParams  ::= EventParams "++Eparam" EventParams    [right, function]
 // -------------------------------------------------------------------------------
    rule .EventParams ++Eparam EPARAMS:EventParams => EPARAMS

    rule (EPARAM EPARAMS1) ++Eparam EPARAMS2 => EPARAM (EPARAMS1 ++Eparam EPARAMS2)


    syntax Exprs  ::= Exprs "++Expr" Exprs    [right, function]
 // ----------------------------------------------------------
    rule .Exprs     ++Expr EXPRS:Exprs => EXPRS

    rule (EXPR EXPRS1) ++Expr EXPRS2 => EXPR (EXPRS1 ++Expr EXPRS2)


    syntax LLLExp   ::= "$%seq" "(" LLLExps ")"
    syntax LLLExps  ::= List{LLLExp, ","}          [klabel("LLLExpList")]
    syntax LLLExps  ::= LLLExps "++LLL" LLLExps    [right, function]
 // ---------------------------------------------------------------
    rule .LLLExps    ++LLL LES:LLLExps => LES

    rule (LE , LES1) ++LLL LES2        => LE , (LES1 ++LLL LES2)


    syntax TypedLLLExps  ::= TypedLLLExps "++TLLL" TypedLLLExps  [right, function]
 // ------------------------------------------------------------------------------
    rule .TypedLLLExps ++TLLL TLLLEXPS:TypedLLLExps => TLLLEXPS

    rule (TLLLEXP TLLLEXPS1) ++TLLL TLLLEXPS2 => TLLLEXP (TLLLEXPS1 ++TLLL TLLLEXPS2)


    syntax Ids   ::= List{Id, ""}
    syntax Ids   ::= Ids "++Id" Ids    [right, function]
    syntax Ids   ::= Ids "++Id" Id     [right, function]
 // ----------------------------------------------------
    rule .Ids ++Id IDS:Ids   => IDS

    rule (ID IDS1) ++Id IDS2 => ID (IDS1 ++Id IDS2)

    rule .Ids ++Id ID        => ID .Ids

    rule (ID1 IDS) ++Id ID   => (ID1 IDS) ++Id (ID .Ids)


// In List
// =======


    syntax Bool  ::= "#inIds" "(" Id "," Ids ")"    [function]
 // ----------------------------------------------------------
    rule #inIds(ID, .Ids) => false

    rule #inIds(ID, ID1 IDS) => true               requires ID ==K ID1

    rule #inIds(ID, ID1 IDS) => #inIds(ID, IDS)    requires ID =/=K ID1


    syntax Bool  ::= "#inDecorators" "(" Decorator "," Decorators ")"  [function]
 // -----------------------------------------------------------------------------
    rule #inDecorators(D, .Decorators) => false

    rule #inDecorators(D, DEC DECS) => true                     requires D ==K DEC

    rule #inDecorators(D, DEC DECS) => #inDecorators(D, DECS)   requires D =/=K DEC


// Size of List
// ============


    syntax Int  ::= "#numOfExprs" "(" Exprs ")"  [function]
 // -------------------------------------------------------
    rule #numOfExprs(.Exprs) => 0

    rule #numOfExprs(EXPR EXPRS) => 1 +Int #numOfExprs(EXPRS)


    syntax Int  ::= "#numOfParams" "(" Params ")"  [function]
 // ---------------------------------------------------------
    rule #numOfParams(.Params) => 0

    rule #numOfParams(PARAM PARAMS) => 1 +Int #numOfParams(PARAMS)


    syntax Int  ::= "#numOfEventParams" "(" EventParams ")"  [function]
 // -------------------------------------------------------------------
    rule #numOfEventParams(.EventParams) => 0

    rule #numOfEventParams(EPARAM EPARAMS) => 1 +Int #numOfEventParams(EPARAMS)


// Type Related
// ============


    syntax Int  ::= "#sizeOfParams" "(" Params ")"    [function]
    syntax Int  ::= "#sizeOfParam"  "(" Param  ")"    [function]
 // ------------------------------------------------------------
    rule #sizeOfParams(.Params) => 0

    rule #sizeOfParams(P PS)    => #sizeOfParam(P) +Int #sizeOfParams(PS)

    rule #sizeOfParam(%param(_, %bytesT(_))) => 32

    rule #sizeOfParam(%param(_, T)) => #sizeOfType(T)    requires notBool isByteArrayType(T)


    syntax Int  ::= "#sizeOfType" "(" Type ")"     [function]
 // ---------------------------------------------------------
    rule #sizeOfType(T:BaseType) => 32

    rule #sizeOfType(%bytesT(L)) => #ceil32(L) +Int 64

    rule #sizeOfType(%listT(T, N)) => #sizeOfType(T) *Int N

    rule #sizeOfType(%structT(.VarDecls)) => 0

    rule #sizeOfType(%structT(%vdecl(_, T) VS)) => #sizeOfType(T) +Int #sizeOfType(%structT(VS))


    syntax String  ::= "#canonicalizeType" "(" Type "," Bool /*is event?*/")"  [function]
 // -------------------------------------------------------------------------------------
    rule #canonicalizeType(%bytesT(L), ISEVENT) => "bytes" +String Int2String(L)
      requires L <=Int 32

    rule #canonicalizeType(%bytesT(L), _) => "bytes"
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


    syntax Int  ::= "#getListTCount" "(" Type ")"    [function]
 // -----------------------------------------------------------
    rule #getListTCount(%listT(T, N)) => N


    // Convert from one base type to another. Need to call `#unwrapLoc` first.
    syntax CTypedLLLExp  ::= "#baseTypeConvert"    "(" TypedLLLExp "," Type /*to*/ ")"
    syntax CTypedLLLExp  ::= "#baseTypeConvertAux" "(" TypedLLLExp "," Type        ")"
 // ----------------------------------------------------------------------------------
    rule #baseTypeConvert(TCODE, TOT) => #baseTypeConvertAux(#unwrapLoc(TCODE), TOT)

    rule #baseTypeConvertAux(@tlll(FROMT, CODE, _), TOT)
        => #ifThenElse(notBool(isBaseType(FROMT)) orBool notBool(isBaseType(TOT)),
                       #exception("Base type conversion from or to non-base type."),
             #ifThenElse(FROMT ==K TOT,
                         @tlll(TOT, CODE, @none),
               #ifThenElse(FROMT ==K %num andBool TOT ==K %decimal,
                           @tlll(TOT, $mul(CODE, @decimalDivisor), @none),
                 #ifThenElse(FROMT ==K %num256 andBool TOT ==K %num,
                             @tlll(TOT, $uclample(CODE, $mload(@maxNumPos)), @none),
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
    rule #computeFuncId(FNAME, PARAMS)
        => String2Base(substrString(Keccak256(#computeFuncSig(Id2String(FNAME) +String "(", PARAMS)), 0, 8), 16)

    rule #computeFuncSig(SIG, %param(_,T) PARAM1 PARAMS)
        => #computeFuncSig(SIG +String #canonicalizeType(T, false) +String "," , PARAM1 PARAMS)

    rule #computeFuncSig(SIG, %param(_,T) .Params)
        => #computeFuncSig(SIG +String #canonicalizeType(T, false), .Params)

    rule #computeFuncSig(SIG, .Params) => SIG +String ")"


// Memory Lookup and Allocation
// ============================


    syntax CTypedLLLExp  ::= "#lookupVar" "(" Var ")"
 // -------------------------------------------------------------
    rule <k> #lookupVar(%var(NAME)) => @tlll(T, LOC, LOCATTR) ... </k>
         <env> %var(NAME) |-> @taddr(T, LOC, LOCATTR) ENV </env>

    rule <k> #lookupVar(%var(NAME))
            => #exception("Undeclared Variable: " +String Id2String(NAME)) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in keys(ENV)

    rule <k> #lookupVar(%svar(NAME)) => @tlll(T, LOC, LOCATTR) ... </k>
         <global> %svar(NAME) |-> @taddr(T, LOC, LOCATTR) GLOBAL </global>

    rule <k> #lookupVar(%svar(NAME))
            => #exception("Persistent variable undeclared: " +String Id2String(NAME)) ... </k>
         <global> GLOBAL </global>
      requires notBool %svar(NAME) in keys(GLOBAL)

    rule #lookupVar(%listelem(V, EXPR))
        => #lookupListVar(#lookupVar(V), #compileValueExpr(EXPR))

    rule #lookupVar(%mapelem(V, EXPR))
        => #lookupMapVar(#lookupVar(V), #compileValueExpr(EXPR))


    syntax CTypedLLLExp  ::= "#lookupListVar" "(" CTypedLLLExp ","
                                                  CTypedLLLExp
                                              ")"      [seqstrict]
 // --------------------------------------------------------------
    rule #lookupListVar(SUBEXPR, INDEXEXPR)
        => #addVarOffset(SUBEXPR, INDEXEXPR)


    syntax CTypedLLLExp  ::= "#lookupMapVar" "(" CTypedLLLExp ","
                                                 CTypedLLLExp
                                             ")"      [seqstrict]
 // -------------------------------------------------------------
    rule #lookupMapVar(BASEEXPR, INDEXEXPR)
        => #addVarOffset(BASEEXPR, INDEXEXPR)


    syntax CTypedLLLExp  ::= "#addVarOffset" "(" TypedLLLExp /*parent*/ ","
                                                 TypedLLLExp /*key*/    ")"
 // -----------------------------------------------------------------------
    rule #addVarOffset(@tlll(%listT(T, N), LOC, LOCATTR), KEYCODE)
        => #addListVarOffset(@tlll(%listT(T, N), LOC, LOCATTR),
                             #baseTypeConvert(KEYCODE, %num))

    rule #addVarOffset(@tlll(%mapT(VT, KT), LOC, LOCATTR), KEYCODE)
        => #addMapVarOffset(@tlll(%mapT(VT, KT), LOC, LOCATTR),
                            #baseTypeConvert(KEYCODE, KT))


    syntax CTypedLLLExp  ::= "#addListVarOffset" "(" CTypedLLLExp ","
                                                     CTypedLLLExp ")"  [seqstrict]
 // -----------------------------------------------------------------------------
    rule #addListVarOffset(@tlll(%listT(T, N), LOC, @locattr(@storage, MUTABLE)),
                           @tlll(_, CODE, _))
        => @tlll(T, $add($sha3_32(LOC), $uclamplt(CODE, N)), @locattr(@storage, MUTABLE))

    rule #addListVarOffset(@tlll(%listT(T, N), LOC, @locattr(@storage_prehashed, MUTABLE)),
                          @tlll(_, CODE, _))
        => @tlll(T, $add(LOC, $uclamplt(CODE, N)), @locattr(@storage, MUTABLE))

    rule #addListVarOffset(@tlll(%listT(T, N), LOC, @locattr(@memory, MUTABLE)),
                           @tlll(_, CODE, _))
        => @tlll(T, $add($mul(#sizeOfType(T), $uclamplt(CODE, N)), LOC), @locattr(@memory, MUTABLE))


    syntax CTypedLLLExp  ::= "#addMapVarOffset" "(" CTypedLLLExp ","
                                                    CTypedLLLExp ")"  [seqstrict]
 // -----------------------------------------------------------------------------
    rule #addMapVarOffset(@tlll(%mapT(VT, KT), LOC, @locattr(@storage, MUTABLE)),
                          @tlll(_, CODE, _))
        => @tlll(VT, $add($sha3_32(LOC), CODE), @locattr(@storage, MUTABLE))

    rule #addMapVarOffset(@tlll(%mapT(VT, KT), LOC, @locattr(@storage_prehashed, MUTABLE)),
                          @tlll(_, CODE, _))
        => @tlll(VT, $add(LOC, CODE), @locattr(@storage, MUTABLE))

    rule #addMapVarOffset(@tlll(%mapT(VT, KT), _, @locattr(@memory, _)), _)
        => #exception("Can only have fixed-side arrays in memory, not mappings")


    syntax CTypedLLLExp  ::= "#newVar" "(" Id "," Type ")"
 // ------------------------------------------------------
    rule <k> #newVar(NAME, T) => @tlll(T, LOC, @locattr(@memory, true)) ...</k>
         <env> ENV => #updateEnv(ENV, %var(NAME), T, LOC, true) </env>
         <nextMem> LOC => LOC +Int #sizeOfType(T) </nextMem>
      requires notBool %var(NAME) in keys(ENV)

    rule <k> #new(NAME, T)
           => #exception("Duplicate variable name: " +String Id2String(NAME)) ...</k>
         <env> ENV </env>
      requires %var(NAME) in keys(ENV)


    syntax CTypedLLLExp  ::= "#lookupOrNewVar" "(" Var "," Type ")"
 // ---------------------------------------------------------------
    rule <k> #lookupOrNewVar(%var(NAME), _) => @tlll(T, LOC, LOCATTR) ... </k>
         <env> %var(NAME) |-> @taddr(T, LOC, LOCATTR) ENV </env>

    rule <k> #lookupOrNewVar(%var(NAME), T) => #newVar(NAME, T) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in keys(ENV)

    rule #lookupOrNewVar(%svar(NAME), _) => #lookupVar(%svar(NAME))

    rule #lookupOrNewVar(%listelem(V, EXPR), _) => #lookupVar(%listelem(V, EXPR))

    rule #lookupOrNewVar(%mapelem(V, EXPR), _) => #lookupVar(%mapelem(V, EXPR))


    syntax CTypedLLLExp  ::= "#newLoopVar" "(" Id ")"
 // -------------------------------------------------
    rule <k> #newLoopVar(NAME) => #lookupVar(%var(NAME)) ... </k>
         <forvar> FORVARS </forvar>
      requires %var(NAME) in FORVARS

    rule <k> #newLoopVar(NAME) => #newVar(NAME, %num) ... </k>
         <forvar> FORVARS (.Set => SetItem(%var(NAME))) </forvar>
      requires notBool %var(NAME) in FORVARS


    syntax CTypedLLLExp  ::= "#newPlaceholder" "(" Type ")"
 // -------------------------------------------------------
    rule <k> #newPlaceholder(T)
           => #newVar(String2Id("_placeholder_" +String Int2String(I)), T) ... </k>
         <placeholder> I => I +Int 1 </placeholder>


    syntax Map  ::= "#updateEnv" "(" Map "," Var "," Type "," Int /*loc*/ "," Bool /*mutable*/ ")"  [function]
    syntax Map  ::= "#flattenStruct" "(" Map "," Var "," VarDecls "," Int "," Bool ")"              [function]
 // ----------------------------------------------------------------------------------------------------------
    rule #updateEnv(M, V, %structT(VARDECLS), LOC, MUTABLE) => #flattenStruct(M, V, VARDECLS, LOC, MUTABLE)

    rule #updateEnv(M, V, T, LOC, MUTABLE) => M[V <- @taddr(T, LOC, @locattr(@memory, MUTABLE))]
      requires notBool isStructType(T)

    rule #flattenStruct(M, V, .VarDecls, LOC, MUTABLE) => M

    rule #flattenStruct(M, V, %vdecl(NAME, T) VS, LOC, MUTABLE)
        => #flattenStruct(#updateEnv(M, %mem(V, NAME), T, LOC, MUTABLE),
                          V, VS, LOC +Int #sizeOfType(T), MUTABLE)



// Others
// ======


    syntax TypedLLLExp ::= "#unwrapLoc" "(" TypedLLLExp ")"  [function]
 // -------------------------------------------------------------------
    rule #unwrapLoc(@tlll(T, CODE, @locattr(@memory, _)))  => @tlll(T, $mload(CODE), @none)

    rule #unwrapLoc(@tlll(T, CODE, @locattr(@storage, _))) => @tlll(T, $sload(CODE), @none)

    rule #unwrapLoc(@tlll(T, CODE, @none))                 => @tlll(T, CODE, @none)


    syntax Int    ::= "#convertToWei" "(" Id ")"  [function]
 // --------------------------------------------------------
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


    syntax KItem  ::= "#ifThen" "(" Bool /*condition*/ "," K /*then*/ ")"  [function]
 // ---------------------------------------------------------------------------------
    rule #ifThen(true, THENCLAUSE) => THENCLAUSE
    rule #ifThen(false, THENCLAUSE) => .


    syntax KItem  ::= "#ifThenElse" "(" Bool /*condition*/ "," K /*then*/ "," K /*else*/ ")"  [function]
 // ----------------------------------------------------------------------------------------------------
    rule #ifThenElse(true, THENCLAUSE, ELSECLAUSE) => THENCLAUSE
    rule #ifThenElse(false, THENCLAUSE, ELSECLAUSE) => ELSECLAUSE


    syntax Int  ::= "#getFirstStoreLoc" "(" LLLExps ")"  [function]
 // ---------------------------------------------------------------
    rule #getFirstStoreLoc($mstore(L:Int, _), CODE) => L


endmodule
