/* Viper source code:
 * https://github.com/ethereum/viper/commit/8c6000b16e11127462506fd0ac632ce535491bec
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
                                       Bool /*private?*/  ")"

    syntax PackedLoggingData  ::= "@loggingdata" "(" LLLExp ","  // code
                                                     Int    ","  // start loc
                                                     Int    ")"  // size

    syntax PackedArgBy32      ::= "@argby32" "(" LLLExps ","  // code
                                                 Int     ")"  // size

    syntax PackedArgData      ::= "@argdata" "(" LLLExp ","  // code
                                                 Int    ")"  // size

    // Convention: C'Sort' is a one-one corresponding supersort of Sort. C'Sort'
    //             requires for evaluation (i.e. not KResult).
    syntax CType               ::= Type
    syntax CBytes              ::= Bytes
    syntax CParams             ::= Params
    syntax CLLLExp             ::= LLLExp
    syntax CLLLExps            ::= LLLExps
    syntax CTypedLLLExp        ::= TypedLLLExp
    syntax CTypedLLLExps       ::= TypedLLLExps
    syntax CEventParams        ::= EventParams
    syntax CPackedArgBy32      ::= PackedArgBy32
    syntax CPackedArgData      ::= PackedArgData
    syntax CPackedLoggingData  ::= PackedLoggingData

    syntax KResult  ::= Int
                      | Bool
                      | Type
                      | Bytes
                      | String
                      | Params
                      | LLLExp
                      | LLLExps
                      | UnitTuple
                      | EventParams
                      | TypedLLLExp
                      | TypedLLLExps
                      | PackedArgBy32
                      | PackedArgData
                      | PackedLoggingData


///////////////////////////////////////////////////////////////////////////////
// Preprocessing
///////////////////////////////////////////////////////////////////////////////


    syntax KItem  ::= "#compileViperToLLL"    "(" Pgm ")"

    syntax KItem  ::= "#compileViperToLLLAux" "(" CLLLExps /*header code*/  ","
                                                  CLLLExps /*init func*/    ","
                                                  CLLLExps /*regular func*/
                                              ")"                   [seqstrict]

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
                         $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0)),.LLLExps)) </lll>

    rule <k> #compileViperToLLLAux(INITIALIZER, OTHERFUNCS) => . ... </k>
         <lll> _ => $%seq(
                      $return(
                        0,
                        $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0)),.LLLExps) </lll>


// Process Events
// ==============


    syntax KItem  ::= "#addEvents"     "(" Events ")"
    syntax KItem  ::= "#addEvent"      "(" Event ")"
    syntax KItem  ::= "#addEventAux"   "(" K "," Id "," CEventParams ")"  [strict(1, 3)]
 // ------------------------------------------------------------------------------------
    rule #addEvents(.Events) => .

    rule #addEvents(E ES) => #addEvent(E) ~> #addEvents(ES)

    rule <k> #addEvent(%event(NAME, EPARAMS))
            => #checkEventParams(EPARAMS, 0, .Ids)
            ~> #addEventAux(#computeEventId(NAME, EPARAMS),
                            NAME,
                            #parseTypeForEventParams(EPARAMS, .EventParams))
         ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool NAME in_keys(SIGS)

    rule <k> #addEvent(%event(NAME, EPARAMS))
            => #exception("Duplicate event name: " +String Id2String(NAME))
         ... </k>
         <internalSig> SIGS </internalSig>
      requires NAME in_keys(SIGS)

    rule <k> #addEventAux(EID:Int, NAME, EPARAMS) => . ... </k>
         <internalSig> SIGS => SIGS[NAME <- @event(EID, NAME, EPARAMS)] </internalSig>


    syntax KItem  ::= "#checkEventParams"      "(" EventParams "," Int "," Ids ")"
    syntax KItem  ::= "#checkEventParamType"   "(" Type ")"
 // ------------------------------------------------------------------------------
    rule #checkEventParams(.EventParams, TOPICNUM, NAMES) => .
      requires TOPICNUM <=Int 3

    rule #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
        => #checkEventParamType(T)
        ~> #ifThen(#inIds(NAME, NAMES),
                   #exception("Duplicate function argument name: " +String Id2String(NAME)))
        ~> #checkEventParams(EPARAMS, TOPICNUM +Int 1, NAMES ++Id (NAME .Ids))
      requires TOPICNUM <Int 3

    rule #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
        => #exception("Maximum of 3 topics.")
      requires TOPICNUM >=Int 3

    rule #checkEventParams(%eparam(NAME, T, false) EPARAMS, TOPICNUM, NAMES)
        => #checkEventParamType(T)
        ~> #ifThen(#inIds(NAME, NAMES),
                   #exception("Duplicate function argument name: " +String Id2String(NAME)))
        ~> #checkEventParams(EPARAMS, TOPICNUM, NAMES ++Id (NAME .Ids))

    rule #checkEventParamType(%bytesT(L)) => .
      requires L <=Int 32

    rule #checkEventParamType(%bytesT(L)) => #exception("Can only log a maximum of 32 bytes at a time.")
      requires L >Int 32

    rule #checkEventParamType(T) => .
      requires notBool isByteArrayType(T)


// Process Globals
// ===============


    syntax KItem  ::= "#addGlobals"   "(" Globals ")"
    syntax KItem  ::= "#addGlobal"    "(" Global  ")"
    syntax KItem  ::= "#addGlobalAux" "(" Id "," CType ")"    [strict(2)]
 // ---------------------------------------------------------------------
    rule #addGlobals(.Globals) => .

    rule #addGlobals(G GS) => #addGlobal(G) ~> #addGlobals(GS)

    rule <k> #addGlobal(%svdecl(NAME, T, _))
            => #addGlobalAux(NAME, #parseType(T, false)) ... </k>
         <global> GLOBALS </global>
      requires notBool %svar(NAME) in_keys(GLOBALS)

    rule <k> #addGlobal(%svdecl(NAME, T, _))
            => #exception("Cannot declare a persistent variable twice! " +String Id2String(NAME))
         ... </k>
         <global> GLOBALS </global>
      requires %svar(NAME) in_keys(GLOBALS)

    rule <k> #addGlobalAux(NAME, T:Type) => . ... </k>
         <global> GLOBALS => GLOBALS[%svar(NAME) <- @taddr(T, LOC, @locattr(@storage, true))] </global>
         <nextStorage> LOC => LOC +Int 1 </nextStorage>


// Process Funcs
// =============


    syntax KItem  ::= "#addFuncs"   "(" Defs ")"

    syntax KItem  ::= "#addFunc"    "(" Id     ","
                                        Params ","
                                        Type   ","
                                        Bool   ","  // constant?
                                        Bool   ","  // payable?
                                        Bool   ","  // private?
                                        Bool   ")"  // public?

    syntax KItem  ::= "#addFuncAux" "(" K       ","  // func id
                                        Id      ","
                                        CParams ","
                                        CType   ","
                                        Bool    ","
                                        Bool    ","
                                        Bool
                                    ")" [strict(1, 3, 4)]
 // -----------------------------------------------------
    rule #addFuncs(.Defs) => .

    rule #addFuncs(%fdecl(DECS, FNAME, PARAMS, T, STMTS) DEFS)
        => #addFunc(FNAME, PARAMS, T,
                    #inDecorators(%@constant, DECS),
                    #inDecorators(%@payable, DECS),
                    #inDecorators(%@private, DECS),
                    #inDecorators(%@public, DECS))
        ~> #addFuncs(DEFS)

    rule <k> #addFunc(FNAME, PARAMS, T, CONSTANT, PAYABLE, PRIVATE, PUBLIC)
            => #checkFuncParams(PARAMS, .Ids)
            ~> #checkPrivatePublicMECE(PRIVATE, PUBLIC)
            ~> #addFuncAux(#computeFuncId(FNAME, PARAMS),
                           FNAME,
                           #parseTypeForParams(PARAMS, .Params),
                           #parseType(T, true),
                           CONSTANT, PAYABLE, PRIVATE)
         ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool FNAME in_keys(SIGS)

    rule <k> #addFunc(FNAME, PARAMS, T, CONSTANT, PAYABLE, PRIVATE, PUBLIC)
            => #exception("Duplicate event or function name: " +String Id2String(FNAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires FNAME in_keys(SIGS)

    rule <k> #addFuncAux(FID:Int, FNAME, PARAMS, T, CONSTANT, PAYABLE, PRIVATE) => . ... </k>
         <internalSig> SIGS
                      => SIGS[FNAME <- @func(FID,
                                             FNAME,
                                             PARAMS,
                                             T,
                                             CONSTANT,
                                             PAYABLE,
                                             PRIVATE)] </internalSig>


    syntax KItem  ::= "#checkFuncParams" "(" Params "," Ids ")"
 // -----------------------------------------------------------
    rule #checkFuncParams(.Params, NAMES) => .

    rule #checkFuncParams(%param(NAME, _) PARAMS, NAMES)
        => #ifThen(#inIds(NAME, NAMES),
                   #exception("Duplicate function argument name: " +String Id2String(NAME)))
        ~> #checkFuncParams(PARAMS, NAMES ++Id (NAME .Ids))


    syntax KItem  ::= "#checkPrivatePublicMECE" "(" Bool /*private?*/ "," Bool /*public?*/ ")"
 // --------------------------------------------------------------------------------------------
    rule #checkPrivatePublicMECE(PRIVATE, PUBLIC)
        => #ifThen(PRIVATE ==K true andBool PUBLIC ==K true,
                   #exception("Cannot use public and private decorators on the same function."))
        ~> #ifThen(PRIVATE ==K false andBool PUBLIC ==K false,
                   #exception("Function visibility must be declared."))


    syntax Defs  ::= "#mkPublicGetters" "(" Globals "," Defs ")"      [function]

    syntax Defs  ::= "#mkPublicGetter"  "(" String /*func name*/ ","
                                            Params               ","
                                            Type                 ","
                                            Var                  ","
                                            Int     /*depth*/    ")"  [function]
 // ----------------------------------------------------------------------------
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

    rule #mkPublicGetter(NAME, PARAMS, %listT(SUBTYPE, L), VAR, DEPTH)
        => #mkPublicGetterListT(NAME, PARAMS, %listT(SUBTYPE, L), VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, %mapT(VT, KT), VAR, DEPTH)
        => #mkPublicGetterMapT(NAME, PARAMS, %mapT(VT, KT), VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, %structT(ANNVARS), VAR, DEPTH)
        => #mkPublicGetterStructT(NAME, PARAMS, %structT(ANNVARS), VAR, DEPTH)


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

    rule #mkPublicGetterListT(NAME, PARAMS, %listT(SUBTYPE, N), VAR, DEPTH)
        => #mkPublicGetter(NAME,
                           PARAMS ++Param (%param(String2Id("arg" +String Int2String(DEPTH)), %num) .Params),
                           SUBTYPE,
                           %subscript(VAR, %var(String2Id("arg" +String Int2String(DEPTH)))),
                           DEPTH +Int 1)

    rule #mkPublicGetterMapT(NAME, PARAMS, %mapT(KT, VT), VAR, DEPTH)
        => #mkPublicGetter(NAME,
                           PARAMS ++Param (%param(String2Id("arg" +String Int2String(DEPTH)), KT) .Params),
                           VT,
                           %subscript(VAR, %var(String2Id("arg" +String Int2String(DEPTH)))),
                           DEPTH +Int 1)

    rule #mkPublicGetterStructT(NAME, PARAMS, %structT(%annvar(VNAME, T) ANNVARS), VAR, DEPTH)
        => #mkPublicGetter(NAME +String "__" +String Id2String(VNAME),
                           PARAMS,
                           T,
                           %attribute(VAR, VNAME),
                           DEPTH)
           ++Def #mkPublicGetterStructT(NAME, PARAMS, %structT(ANNVARS), VAR, DEPTH)

    rule #mkPublicGetterStructT(NAME, PARAMS, %structT(.AnnVars), VAR, DEPTH)
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
    rule <k> #compileFunc(%fdecl(_, FNAME, _, _, STMTS))
            => #compileFuncAux(#copyArg(PARAMS, #isInitFunc(FNAME)),
                               #addClampersForDecorators(PAYABLE, PRIVATE),
                               #fillParams(PARAMS, 0, #isInitFunc(FNAME), .LLLExps),
                               #compileStmts(STMTS, .LLLExps),
                               FUNCID,
                               #isInitFunc(FNAME))
           ~> #clearConfig ... </k>
         <internalSig> FNAME |-> @func(FUNCID, FNAME, PARAMS, RT, CONSTANT, PAYABLE, PRIVATE) SIGS</internalSig>
         <return> _ => RT </return>
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
    syntax LLLExps   ::= "#checkPrivate"   "(" Bool ")"        [function]
 // ----------------------------------------------------------------------
    rule #addClampersForDecorators(PAYABLE, PRIVATE) => #checkPayable(PAYABLE) ++LLL #checkPrivate(PRIVATE)

    rule #checkPayable(true) => .LLLExps

    rule #checkPayable(false) => $assert($iszero($callvalue)),.LLLExps

    rule #checkPrivate(true) => $assert($eq($caller, $address)),.LLLExps

    rule #checkPrivate(false) => .LLLExps


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
         <env> ENV => ENV[%var(NAME) <- @taddr(%bytesT(L), LOC, @locattr(@memory, false))] </env>
         <nextMem> LOC => LOC +Int #sizeOfType(%bytesT(L)) </nextMem>

    rule <k> #fillParam(%param(NAME, T), DATAPOS, ISINIT) => #mkClamper(T, DATAPOS, LOC, ISINIT) ... </k>
         <env> ENV => ENV[%var(NAME) <- @taddr(T, @reservedMemPos +Int DATAPOS, @locattr(@memory, false))] </env>
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

    rule #mkClamper(%unitT(%num, _:Map, _), DPOS, MPOS, ISINIT) => $clamp(
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

    rule #mkClamper(%listT(SUBTYPE, N), DPOS, MPOS, ISINIT) => $%seq(#mkClamperListT(N, SUBTYPE, DPOS, MPOS, ISINIT)),.LLLExps

    rule #mkClamperListT(1, T, DPOS, MPOS, ISINIT) => #mkClamper(T, DPOS, MPOS, ISINIT)

    rule #mkClamperListT(N, T, DPOS, MPOS, ISINIT)
        => #mkClamper(T, DPOS, MPOS, ISINIT) ++LLL
           #mkClamperListT(N -Int 1, T, DPOS +Int #sizeOfType(T), MPOS +Int #sizeOfType(T), ISINIT)
      requires N >Int 1

    rule #mkClamper(%decimal, _, _, _) => $pass,.LLLExps

    rule #mkClamper(%unitT(%decimal, _:Map, _), _, _, _) => $pass,.LLLExps

    rule #mkClamper(%num256, _, _, _) => $pass,.LLLExps

    rule #mkClamper(%bytes32, _, _, _) => $pass,.LLLExps

    rule #mkClamper(%mapT(_, _), _, _, _) => $pass,.LLLExps

    rule #mkClamper(%structT(_), _, _, _) => $pass,.LLLExps

    rule #mkCopier(MPOS, POS, SIZE, true) => $codecopy(MPOS, $add($codelen, POS), SIZE)

    rule #mkCopier(MPOS, POS, SIZE, false) => $calldatacopy(MPOS, $add(4, POS), SIZE)

    rule #mkDataDecl(DATAPOS, true) => $codeload($add($codelen, DATAPOS))

    rule #mkDataDecl(DATAPOS, false) => $calldataload($add(4, DATAPOS))


// Clear configuartion
// ===================


    syntax KItem  ::= "#clearConfig"
 // --------------------------------
    rule <k> CODE:LLLExps ~> (#clearConfig => .) ...</k>
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


    rule #compileStmt(%annvar(NAME, T)) => #annassign(NAME, #parseType(T, true))


    syntax CLLLExps  ::= "#annassign" "(" Id "," CType ")"    [strict(2)]
 // ---------------------------------------------------------------------
    rule #annassign(NAME, T) => #newVar(NAME, T) ~> $pass,.LLLExps

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

    rule #getTarget(%attribute(V, FIELD), TCODE) => #getTargetAux(TCODE)

    rule <k> #getTarget(%subscript(V, INDEX), TCODE)
            => #exception("Altering list while being iterated!") ... </k>
         <inLoop> INLOOP </inLoop>
      requires V in INLOOP

    rule <k> #getTarget(%subscript(V, INDEX), TCODE) => #getTargetAux(TCODE) ... </k>
         <inLoop> INLOOP </inLoop>
      requires notBool V in INLOOP

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
        => #ifThen(notBool(isByteArrayType(RT)),
                   #exception("Setter type mismatch: left side is byte array but right side is not."))
        ~> #mkSetterBytesT(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
      requires isByteArrayType(LT)

    // Can't copy mappings
    rule #mkSetter(@tlll(LT, LOC, LOCATTR), RTCODE)
        => #exception("Cannot copy mappings; can only copy individual elements.")
      requires isMappingType(LT)

    rule #mkSetter(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
        => #ifThen(notBool(isListType(RT)),
                   #exception("Setter type mismatch: left side is array but right side is not."))
        ~> #mkSetterListT(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
      requires isListType(LT)

    rule #mkSetter(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
        => #ifThen(notBool(isStructType(RT)),
                   #exception("Setter type mismatch: left side is struct but right side is not."))
        ~> #mkSetterStructT(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
      requires isStructType(LT)


    // Basic Types
    syntax CLLLExps  ::= "#mkSetterBase"  "(" TypedLLLExp "," CTypedLLLExp ")"  [strict(2)]
 // ---------------------------------------------------------------------------------------
    rule #mkSetterBase(@tlll(_, LOC, @locattr(@storage, _)), @tlll(_, CODE, _))
        => $sstore(LOC, CODE),.LLLExps

    rule #mkSetterBase(@tlll(_, LOC, @locattr(@memory, _)), @tlll(_, CODE, _))
        => $mstore(LOC, CODE),.LLLExps


    // Byte array
    syntax CLLLExps  ::= "#mkSetterBytesT" "(" TypedLLLExp "," TypedLLLExp ")"
 // --------------------------------------------------------------------------
    rule #mkSetterBytesT(LTCODE, RTCODE) => #mkByteArrayCopier(LTCODE, RTCODE)


    // List
    syntax CLLLExps  ::= "#mkSetterListT" "(" TypedLLLExp "," TypedLLLExp ")"

    syntax CLLLExps  ::= "#mkSetterListTAux" "(" TypedLLLExp ","  // left
                                                 TypedLLLExp ","  // left token
                                                 TypedLLLExp ")"  // right
 // ------------------------------------------------------------
    rule #mkSetterListT(@tlll(LT, LCODE, @locattr(LTARGET, LMUTABLE)),
                        @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(#getListTCount(LT) =/=K #getListTCount(RT),
                   #exception("Mismatched number of elements in left and right side arrays."))
        ~> #ifThenElse(LTARGET ==K @storage,
                       #mkSetterListTAux(@tlll(LT, $sha3_32(LCODE), @locattr(@storage_prehashed, LMUTABLE)),
                                         @tlll(LT, $_L, @locattr(@storage_prehashed, LMUTABLE)),
                                         @tlll(RT, RCODE, REXPRATTR)),
                       #mkSetterListTAux(@tlll(LT, LCODE, @locattr(LTARGET, LMUTABLE)),
                                         @tlll(LT, $_L, @locattr(LTARGET, LMUTABLE)),
                                         @tlll(RT, RCODE, REXPRATTR)))

    rule #mkSetterListTAux(@tlll(LT, LCODE, _), LTTOKENCODE, @tlll(RT, RCODE, REXPRATTR))
        => #mkSetterListTLiteral(LT, LCODE, LTTOKENCODE, 0, RCODE, .LLLExps)
      requires isMultiLLLExp(RCODE)

    rule #mkSetterListTAux(@tlll(LT, LCODE, _), LTTOKENCODE, @tlll(RT, RCODE, RLOCATTR))
        => #mkSetterListTVar(LT, LCODE, LTTOKENCODE, 0, RCODE,
                             @tlll(RT, $_R, RLOCATTR), .LLLExps)
      requires notBool isMultiLLLExp(RCODE)


    syntax CLLLExps  ::= "#mkSetterListTLiteral" "(" Type         ","  // left list type
                                                     LLLExp       ","  // left code
                                                     TypedLLLExp  ","  // left token
                                                     Int          ","  // index
                                                     LLLExp       ","  // right code
                                                     LLLExps      ")"  // result code
 // -------------------------------------------------------------------------------
    rule #mkSetterListTLiteral(%listT(SUBTYPE, N), LCODE, LTTOKENCODE, INDEX, $multi(TEXPR TEXPRS), RESULTCODE)
        => #mkSetter(#addVarOffset(LTTOKENCODE, @tlll(%num, INDEX, @none)), TEXPR)
        ~> #mkSetterListTLiteral(%listT(SUBTYPE, N), LCODE, LTTOKENCODE, INDEX, $multi(TEXPRS), RESULTCODE)
      requires INDEX <Int N

    rule #mkSetterListTLiteral(%listT(SUBTYPE, N), LCODE, _, INDEX, _, RESULTCODE)
        => $with($_L, LCODE, $%seq(RESULTCODE)),.LLLExps
      requires INDEX ==Int N

    rule CODE:LLLExps ~> #mkSetterListTLiteral(LT, LCODE, LTTOKENCODE, INDEX, RCODE, RESULTCODE)
        => #mkSetterListTLiteral(LT, LCODE, LTTOKENCODE, INDEX +Int 1, RCODE, RESULTCODE ++LLL CODE)


    syntax CLLLExps  ::= "#mkSetterListTVar" "(" Type        ","  // left list type
                                                 LLLExp      ","  // left code
                                                 TypedLLLExp ","  // left token
                                                 Int         ","  // index
                                                 LLLExp      ","  // right code
                                                 TypedLLLExp ","  // right token
                                                 LLLExps     ")"  // result code
  // --------------------------------------------------------------------------------
     rule #mkSetterListTVar(%listT(SUBTYPE, N), LCODE, LTTOKENCODE, INDEX, RCODE, RTTOKENCODE, RESULTCODE)
         => #mkSetter(#addVarOffset(LTTOKENCODE, @tlll(%num, INDEX, @none)),
                      #addVarOffset(RTTOKENCODE, @tlll(%num, INDEX, @none)))
         ~> #mkSetterListTVar(%listT(SUBTYPE, N), LCODE, LTTOKENCODE, INDEX, RCODE, RTTOKENCODE, RESULTCODE)
       requires INDEX <Int N

     rule #mkSetterListTVar(%listT(SUBTYPE, N), LCODE, _, INDEX, RCODE, _, RESULTCODE)
         => $with($_L, LCODE, $with($_R, RCODE, $%seq(RESULTCODE))),.LLLExps
       requires INDEX ==Int N

     rule CODE:LLLExps ~> #mkSetterListTVar(LT, LCODE, LTTOKENCODE, INDEX, RCODE, RTTOKENCODE, RESULTCODE)
         => #mkSetterListTVar(LT, LCODE, LTTOKENCODE, INDEX +Int 1, RCODE, RTTOKENCODE, RESULTCODE ++LLL CODE)


    // Struct
    syntax CLLLExps  ::= "#mkSetterStructT" "(" TypedLLLExp "," TypedLLLExp ")"

    syntax CLLLExps  ::= "#mkSetterStructTAux" "(" TypedLLLExp ","  // left
                                                   TypedLLLExp ","  // left token
                                                   TypedLLLExp ")"  // right
 // ---------------------------------------------------------------------------
    rule #mkSetterStructT(@tlll(%structT(LANNVARS), LCODE, @locattr(LTARGET, LMUTABLE)),
                          @tlll(%structT(RANNVARS), RCODE, REXPRATTR))
        => #checkStructFieldNameMatch(LANNVARS, RANNVARS)
        ~> #ifThenElse(LTARGET ==K @storage,
                       #mkSetterStructTAux(@tlll(%structT(LANNVARS), $sha3_32(LCODE), @locattr(@storage_prehashed, LMUTABLE)),
                                           @tlll(%structT(LANNVARS), $_L, @locattr(@storage_prehashed, LMUTABLE)),
                                           @tlll(%structT(RANNVARS), RCODE, REXPRATTR)),
                       #mkSetterStructTAux(@tlll(%structT(LANNVARS), LCODE, @locattr(LTARGET, LMUTABLE)),
                                           @tlll(%structT(LANNVARS), $_L, @locattr(LTARGET, LMUTABLE)),
                                           @tlll(%structT(RANNVARS), RCODE, REXPRATTR)))

    rule #mkSetterStructTAux(@tlll(%structT(LANNVARS), LCODE, _), LTTOKENCODE, @tlll(RT, RCODE, REXPRATTR))
        => #mkSetterStructTLiteral(LANNVARS, LCODE, LTTOKENCODE, RCODE, .LLLExps)
      requires isMultiLLLExp(RCODE)

    rule #mkSetterStructTAux(@tlll(%structT(LANNVARS), LCODE, _), LTTOKENCODE, @tlll(RT, RCODE, RLOCATTR))
        => #mkSetterStructTVar(LANNVARS, LCODE, LTTOKENCODE, RCODE,
                               @tlll(RT, $_R, RLOCATTR), .LLLExps)
      requires notBool isMultiLLLExp(RCODE)


    syntax KItem  ::= "#checkStructFieldNameMatch" "(" AnnVars "," AnnVars ")"
 // -----------------------------------------------------------------------
    rule #checkStructFieldNameMatch(.AnnVars, .AnnVars) => .

    rule #checkStructFieldNameMatch(%annvar(LNAME, _) LANNVARS, %annvar(RNAME, _) RANNVARS)
        => #checkStructFieldNameMatch(LANNVARS, RANNVARS)
      requires LNAME ==K RNAME

    rule #checkStructFieldNameMatch(%annvar(LNAME, _) LANNVARS, %annvar(RNAME, _) RANNVARS)
        => #exception("Keys don't match for structs.")
      requires LNAME =/=K RNAME

    rule #checkStructFieldNameMatch(%annvar(LNAME, _) LANNVARS, .AnnVars)
        => #exception("Keys don't match for structs.")

    rule #checkStructFieldNameMatch(.AnnVars, %annvar(RNAME, _) RANNVARS)
        => #exception("Keys don't match for structs.")


    syntax CLLLExps  ::= "#mkSetterStructTLiteral" "(" AnnVars     ","  // left struct fields
                                                       LLLExp      ","  // left code
                                                       TypedLLLExp ","  // left token
                                                       LLLExp      ","  // right code
                                                       LLLExps     ")"  // result code
 // ------------------------------------------------------------------
    rule #mkSetterStructTLiteral(.AnnVars, LCODE, _, _, RESULTCODE)
        => $with($_L, LCODE, $%seq(RESULTCODE)), .LLLExps

    rule #mkSetterStructTLiteral(%annvar(NAME, T) ANNVARS, LCODE, LTTOKENCODE, $multi(TEXPR TEXPRS), RESULTCODE)
        => #mkSetter(#addVarOffset(LTTOKENCODE, @tlll(%void, NAME, @none)), TEXPR)
        ~> #mkSetterStructTLiteral(ANNVARS, LCODE, LTTOKENCODE, $multi(TEXPRS), RESULTCODE)

    rule CODE:LLLExps ~> #mkSetterStructTLiteral(ANNVARS, LCODE, LTTOKENCODE, RCODE, RESULTCODE)
        => #mkSetterStructTLiteral(ANNVARS, LCODE, LTTOKENCODE, RCODE, RESULTCODE ++LLL CODE)


    syntax CLLLExps  ::= "#mkSetterStructTVar" "(" AnnVars     ","  // left struct fields
                                                   LLLExp      ","  // left code
                                                   TypedLLLExp ","  // left token
                                                   LLLExp      ","  // right code
                                                   TypedLLLExp ","  // right token
                                                   LLLExps     ")"  // result code
 // -------------------------------------------------------------
    rule #mkSetterStructTVar(.AnnVars, LCODE, _, RCODE, _, RESULTCODE)
        => $with($_L, LCODE, $with($_R, RCODE, $%seq(RESULTCODE))),.LLLExps

    rule #mkSetterStructTVar(%annvar(NAME, T) ANNVARS, LCODE, LTTOKENCODE, RCODE, RTTOKENCODE, RESULTCODE)
        => #mkSetter(#addVarOffset(LTTOKENCODE, @tlll(%void, NAME, @none)),
                     #addVarOffset(RTTOKENCODE, @tlll(%void, NAME, @none)))
        ~> #mkSetterStructTVar(ANNVARS, LCODE, LTTOKENCODE, RCODE, RTTOKENCODE, RESULTCODE)

    rule CODE:LLLExps ~> #mkSetterStructTVar(ANNVARS, LCODE, LTTOKENCODE, RCODE, RTTOKENCODE, RESULTCODE)
        => #mkSetterStructTVar(ANNVARS, LCODE, LTTOKENCODE, RCODE, RTTOKENCODE, RESULTCODE ++LLL CODE)


// Aug Assignment
// ==============


    rule #compileStmt(%augassign(OP, V, E)) => #augassign(OP,
                                                          #getTarget(V, #compileLocExpr(V)),
                                                          #compileValueExpr(E))


    syntax CLLLExps  ::= "#augassign"    "(" AugAssignOp  ","
                                             CTypedLLLExp ","  // variable loc
                                             CTypedLLLExp      // compiled expr
                                         ")"  [seqstrict(2,3)]

    syntax CLLLExps  ::= "#augassignAux" "(" AugAssignOp  ","
                                             CTypedLLLExp ","
                                             TypedLLLExp  ")"
 // ---------------------------------------------------------
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


    syntax CTypedLLLExp  ::= "#convertToBinaryArith" "(" AugAssignOp ","
                                                         TypedLLLExp ","  // left
                                                         TypedLLLExp ")"  // right
 // --------------------------------------------------------------------
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


    syntax CLLLExps  ::= "#ifstmt" "(" CTypedLLLExp ","  // Test
                                       CLLLExps     ","  // Then
                                       CLLLExps          // Else
                                   ")"      [seqstrict]

    syntax CLLLExps  ::= "#ifstmt" "(" CTypedLLLExp ","  // Test
                                       CLLLExps          // Then
                                   ")"      [seqstrict]
 // ---------------------------------------------------
    rule #compileStmt(%if(TEST, THENSTMTS, ELSESTMTS))
        => #ifstmt(#compileValueExpr(TEST),
                   #compileStmts(THENSTMTS, .LLLExps),
                   #compileStmts(ELSESTMTS, .LLLExps))

    rule #compileStmt(%if(TEST, THENSTMTS)) => #ifstmt(#compileValueExpr(TEST), #compileStmts(THENSTMTS, .LLLExps))

    rule #ifstmt(@tlll(_, CODE, _), THEN:LLLExps, ELSE:LLLExps) => $if(CODE, $%seq(THEN), $%seq(ELSE)),.LLLExps

    rule #ifstmt(@tlll(_, CODE, _), THEN:LLLExps) => $if(CODE, $%seq(THEN)),.LLLExps


// For Loop
// ========


    // e.g. for i in range(10): ...
    rule #compileStmt(%forrange(ITER, ROUNDS, STMTS))
        => #forrange(#newLoopVar(ITER, %num), @tlll(%num, 0, @none), ROUNDS, #compileStmts(STMTS, .LLLExps))
        ~> #clearIter(ITER)

    // e.g. for i in range(100, 110): ...
    rule #compileStmt(%forrange(ITER, START:Int, END:Int, STMTS))
        => #forrange(#newLoopVar(ITER, %num), @tlll(%num, START, @none), END -Int START, #compileStmts(STMTS, .LLLExps))
        ~> #clearIter(ITER)

    // e.g. for i in range(x, x + 10): ...
    rule #compileStmt(%forrange(ITER, %var(V), %binop(+, %var(V), ROUNDS:Int), STMTS))
        => #forrange(#newLoopVar(ITER, %num), #compileValueExpr(%var(V)), ROUNDS, #compileStmts(STMTS, .LLLExps))
        ~> #clearIter(ITER)

    // e.g. for i in list(): ...
    rule #compileStmt(%forlist(ITER, EXPR, STMTS))
        => #forlist(ITER, EXPR, #compileExpr(EXPR), STMTS)
        ~> #clearIter(ITER)
        ~> #clearVar(String2Id("_index_for_" +String Id2String(ITER)))


    syntax CLLLExps  ::= "#forrange" "(" CTypedLLLExp ","
                                         CTypedLLLExp ","  // start
                                         Int          ","  // rounds
                                         CLLLExps          // body code
                                     ")"  [seqstrict(1,2,4)]
 // --------------------------------------------------------
    rule #forrange(@tlll(%num, LOC:Int, _), @tlll(_, STARTCODE, _), ROUNDS, BODYCODE:LLLExps)
        => $repeat(LOC, STARTCODE, ROUNDS, $%seq(BODYCODE)),.LLLExps


    syntax CLLLExps  ::= "#forlist" "(" Id           ","
                                        Expr         ","
                                        CTypedLLLExp ","
                                        Stmts
                                    ")"    [strict(3)]

    syntax CLLLExps  ::= "#forlistAux" "(" CTypedLLLExp ","  // iter
                                           CTypedLLLExp ","  // index for iter
                                           Expr         ","  // list expr
                                           TypedLLLExp  ","  // list
                                           Stmts
                                       ")"  [seqstrict(1, 2)]
 // ---------------------------------------------------------
    rule #forlist(ITER, EXPR, @tlll(%listT(SUBTYPE, N), CODE, EXPRATTR), STMTS)
        => #ifThen(notBool(isBaseType(SUBTYPE)),
                   #exception("For loops allowed only on basetype lists."))
        ~> #forlistAux(#newLoopVar(ITER, SUBTYPE),
                       #newVar(String2Id("_index_for_" +String Id2String(ITER)), %num),
                       EXPR,
                       @tlll(%listT(SUBTYPE, N), CODE, EXPRATTR),
                       STMTS)

    rule #forlistAux(TITERCODE, TINDEXCODE, EXPR, @tlll(%listT(SUBTYPE, N), CODE, EXPRATTR), STMTS)
        => #forlistliteral(TITERCODE, TINDEXCODE,
                           #newPlaceholder(%listT(SUBTYPE, N)),
                           @tlll(%listT(SUBTYPE, N), CODE, EXPRATTR),
                           STMTS)
      requires isListExpr(EXPR)

    rule #forlistAux(TITERCODE, TINDEXCODE, VAR, @tlll(%listT(SUBTYPE, N), LOC, LOCATTR), STMTS)
        => #setInLoop(VAR)
        ~> #forlistvariable(TITERCODE, TINDEXCODE,
                            @tlll(%listT(SUBTYPE, N), LOC, LOCATTR),
                            #compileStmts(STMTS, .LLLExps))
        ~> #removeInLoop(VAR)
      requires isVar(VAR)


    syntax CLLLExps  ::= "#forlistliteral" "(" TypedLLLExp  ","  // iter
                                               TypedLLLExp  ","  // index
                                               CTypedLLLExp ","  // tmp list
                                               TypedLLLExp  ","  // list
                                               Stmts
                                           ")"      [strict(3)]

    syntax CLLLExps  ::= "#forlistliteralAux" "(" TypedLLLExp ","  // iter
                                                  TypedLLLExp ","  // index for iter
                                                  TypedLLLExp ","  // tmp list
                                                  CLLLExps    ","  // setter
                                                  CLLLExps         // stmts
                                              ")"   [seqstrict(4, 5)]
 // -----------------------------------------------------------------
    rule #forlistliteral(TITERCODE, TINDEXCODE, TMPLIST, LISTCODE, STMTS)
        => #forlistliteralAux(TITERCODE,
                              TINDEXCODE,
                              TMPLIST,
                              #mkSetter(TMPLIST, LISTCODE),
                              #compileStmts(STMTS, .LLLExps))

    rule #forlistliteralAux(@tlll(_, ITERLOC, _),
                            @tlll(_, INDEXLOC, _),
                            @tlll(%listT(SUBTYPE, N), TMPLISTLOC, _),
                            SETTERCODE,
                            BODYCODE)
        => $%seq(
             SETTERCODE ++LLL
             ($repeat(INDEXLOC, 0, N, $%seq(
                                        $mstore(ITERLOC, $mload($add(TMPLISTLOC, $mul($mload(INDEXLOC), 32)))),
                                        $%seq(BODYCODE),.LLLExps)),.LLLExps)),.LLLExps


    syntax CLLLExps  ::= "#forlistvariable" "(" TypedLLLExp  ","  // iter
                                                TypedLLLExp  ","  // index for iter
                                                TypedLLLExp  ","  // list
                                                CLLLExps          // stmts
                                            ")"      [strict(4)]
 // ------------------------------------------------------------------------------------------
    // List allocated in memory
    rule #forlistvariable(@tlll(_, ITERLOC, _),
                          @tlll(_, INDEXLOC, _),
                          @tlll(%listT(SUBTYPE, N), LISTLOC, @locattr(@memory, _)),
                          BODYCODE)
        => $repeat(INDEXLOC, 0, N, $%seq(
                                     $mstore(ITERLOC, $mload($add(LISTLOC, $mul($mload(INDEXLOC), 32)))),
                                     $%seq(BODYCODE),.LLLExps)),.LLLExps

    // List allocated in storage
    rule #forlistvariable(@tlll(_, ITERLOC, _),
                          @tlll(_, INDEXLOC, _),
                          @tlll(%listT(SUBTYPE, N), LISTLOC, @locattr(@storage, _)),
                          BODYCODE)
        => $%seq(
             $repeat(INDEXLOC, 0, N, $%seq(
                                       $mstore(ITERLOC, $sload($add($sha3_32(LISTLOC), $mload(INDEXLOC)))),
                                       $%seq(BODYCODE),.LLLExps)),.LLLExps),.LLLExps


    syntax KItem  ::= "#setInLoop" "(" Var ")"
 // ------------------------------------------
    rule <k> #setInLoop(VAR) => . ... </k>
         <inLoop> (.Set => SetItem(VAR)) INLOOPS </inLoop>


    syntax KItem  ::= "#removeInLoop" "(" Var ")"
 // ---------------------------------------------
    rule <k> CODE:LLLExps ~> (#removeInLoop(VAR) => .) ... </k>
         <inLoop> (SetItem(VAR) => .Set) INLOOPS </inLoop>


    syntax KItem  ::= "#clearIter" "(" Id ")"
 // -------------------------------------------------
    rule <k> CODE:LLLExps ~> (#clearIter(ITER) => .) ... </k>
         <env> (%var(ITER) |-> _ => .Map) ENV </env>
         <forvar> (SetItem(%var(ITER)) => .Set) FORVARS </forvar>


    syntax KItem  ::= "#clearVar" "(" Id ")"
 // -------------------------------------------------
    rule <k> CODE:LLLExps ~> (#clearVar(NAME) => .) ... </k>
         <env> (%var(NAME) |-> _ => .Map) ENV </env>


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
    // Base Type
    rule #return(@tlll(T, CODE, EXPRATTR), RETURNTYPE)
        => #ifThen(notBool(isBaseType(RETURNTYPE)),
                   #exception("Trying to return base type but output expecting non base type."))
        ~> #returnBase(#unwrapLoc(@tlll(T, CODE, EXPRATTR)), RETURNTYPE)
      requires isBaseType(T)

    // Byte Array Type
    rule #return(@tlll(T, CODE, EXPRATTR), RETURNTYPE)
        => #ifThen(notBool(isByteArrayType(RETURNTYPE)),
                   #exception("Trying to return byte array type but it not matching the expected return type."))
        ~> #returnBytesT(@tlll(T, CODE, EXPRATTR), RETURNTYPE)
      requires isByteArrayType(T)

    // List Type
    rule #return(@tlll(%listT(SUBTYPE1, N1), CODE, EXPRATTR), %listT(SUBTYPE2, N2))
        => #ifThen(N1 =/=Int N2,
                   #exception("Return list length doesn't match the expected length."))
        ~> #returnListT(@tlll(%listT(SUBTYPE1, N1), CODE, EXPRATTR), %listT(SUBTYPE2, N2))

    // TODO: support return Tuple


    syntax CLLLExps  ::= "#returnBase"    "(" TypedLLLExp "," Type ")"
    syntax CLLLExps  ::= "#returnBaseAux" "(" TypedLLLExp "," Type ")"
 // ------------------------------------------------------------------
    rule #returnBase(@tlll(T, CODE, EXPRATTR), RETURNTYPE)
        => #ifThenElse(#areUnitsCompatible(T, RETURNTYPE, #isNumLiteral(CODE)),
                       #returnBaseAux(@tlll(#dropUnit(T), CODE, EXPRATTR), #dropUnit(RETURNTYPE)),
                       #exception("Return type units mismatch"))

    rule #returnBaseAux(@tlll(T, CODE, _), RETURNTYPE)
        => #ifThenElse((T ==K RETURNTYPE) orBool (T ==K %num andBool RETURNTYPE ==K %signed256),
                       $%seq($mstore(0, CODE), $return(0, 32),.LLLExps),.LLLExps,
                       #exception("Unsupported type conversion."))


    syntax CLLLExps  ::= "#returnBytesT"    "(" TypedLLLExp "," Type ")"
    syntax CLLLExps  ::= "#returnBytesTAux" "(" TypedLLLExp ")"
 // -----------------------------------------------------------------------
    rule #returnBytesT(@tlll(%bytesT(L1), CODE, LOCATTR), %bytesT(L2))
        => #ifThen(L1 >Int L2,
                   #exception("Cannot cast from greater max-length to shorter max-length."))
        ~> #returnBytesTAux(@tlll(%bytesT(L1), CODE, LOCATTR))

    rule #returnBytesTAux(@tlll(%bytesT(L), CODE, @locattr(@memory, _)))
        => $with(
             $_loc,
             CODE,
             $%seq(
               $mstore($sub($_loc, 32), 32),
               $return($sub($_loc, 32), $ceil32($add($mload($_loc), 64))),.LLLExps)),.LLLExps

    rule <k> #returnBytesTAux(@tlll(%bytesT(L), CODE, @locattr(@storage, MUTABLE)))
            => #returnBytesTFromStorage(
                   #mkByteArrayCopier(@tlll(%bytesT(L), LOC +Int 32, @locattr(@memory, true)),
                                      @tlll(%bytesT(L), CODE       , @locattr(@storage, MUTABLE))))
         ... </k>
         <nextMem> LOC </nextMem>


    syntax CLLLExps  ::= "#returnBytesTFromStorage" "(" CLLLExps ")"  [strict]
 // --------------------------------------------------------------------------
    rule <k> #returnBytesTFromStorage(CODE)
            => $%seq(
                 CODE ++LLL
                 ($mstore(LOC, 32),
                  $return(LOC, $add($ceil32($mload(LOC +Int 32)), 64)),.LLLExps)),.LLLExps
         ... </k>
         <nextMem> LOC </nextMem>


    syntax CLLLExps  ::= "#returnListT" "(" TypedLLLExp ","
                                            Type        ")"
 // -------------------------------------------------------
    rule #returnListT(@tlll(%listT(SUBTYPE1, N), CODE, EXPRATTR), %listT(SUBTYPE2, N))
        => #ifThenElse(#isInMemory(EXPRATTR) andBool
                       (SUBTYPE1 ==K SUBTYPE2) andBool
                       (notBool(isMultiLLLExp(CODE))),
                       $return(CODE, #sizeOfType(%listT(SUBTYPE2, N))),
                       #returnListTByCopy(#newPlaceholder(%listT(SUBTYPE2, N)),
                                          @tlll(%listT(SUBTYPE1, N), CODE, EXPRATTR),
                                          %listT(SUBTYPE2, N)))


    syntax CLLLExps  ::= "#returnListTByCopy" "(" CTypedLLLExp ","  // placeholder
                                                  TypedLLLExp  ","
                                                  Type
                                              ")"      [strict(1)]

    syntax CLLLExps  ::= "#returnListTByCopyAux" "(" CLLLExps     ","
                                                     Int          ","
                                                     Type
                                                 ")"      [strict(1)]
 // -----------------------------------------------------------------
    rule #returnListTByCopy(@tlll(T, LOC, LOCATTR), TCODE, RETURNTYPE)
        => #returnListTByCopyAux(#mkSetter(@tlll(T, LOC, LOCATTR), TCODE),
                               LOC, RETURNTYPE)

    rule #returnListTByCopyAux(SETTER, LOC, RETURNTYPE)
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


// Log
// ====


    rule <k> #compileStmt(%log(NAME, ARGS)) => #log(ARGS, EVENTRECORD) ... </k>
         <internalSig> NAME |-> EVENTRECORD:EventRecord SIGS </internalSig>

    rule <k> #compileStmt(%log(NAME, _))
            => #exception("Event not declared yet: " +String Id2String(NAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool NAME in_keys(SIGS)


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
                 #packLoggingTopic(TARG1, TEPARAM1),
                 #packLoggingData(DARGS, DEPARAMS))

    // 2 topics
    rule #logAux(EID, .Exprs, .EventParams, (TARG1 TARG2 .Exprs), (TEPARAM1 TEPARAM2 .EventParams), DARGS, DEPARAMS)
        => #log3(EID,
                 #packLoggingTopic(TARG1, TEPARAM1),
                 #packLoggingTopic(TARG2, TEPARAM2),
                 #packLoggingData(DARGS, DEPARAMS))

    // 3 topics
    rule #logAux(EID, .Exprs, .EventParams, (TARG1 TARG2 TARG3 .Exprs), (TEPARAM1 TEPARAM2 TEPARAM3 .EventParams), DARGS, DEPARAMS)
        => #log4(EID,
                 #packLoggingTopic(TARG1, TEPARAM1),
                 #packLoggingTopic(TARG2, TEPARAM2),
                 #packLoggingTopic(TARG3, TEPARAM3),
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


    syntax CPackedArgBy32  ::= "#packArgBy32" "(" CTypedLLLExp ","  // placeholder
                                                  Expr         ","  // value
                                                  Type
                                              ")"      [strict(1)]
 // --------------------------------------------------------------
    // Base Type
    rule #packArgBy32(@tlll(_, LOC:Int, _), EXPR, T)
        => #packArgBy32Base(LOC, #compileExpr(EXPR), T)
      requires isBaseType(T)

    // Viper only allows 32-byte byte array as data.
    // String Literal
    rule #packArgBy32(@tlll(_, LOC:Int, _), STR:String, %bytesT(L))
        => #ifThen(lengthString(STR) >Int L,
                   #exception("Data input bytes are too big."))
        ~> #ifThen(lengthString(STR) >Int 32,
                   #exception("Can only log a maximum of 32 bytes at a time."))
        ~> #packArgBy32StringLiteral(LOC, #string2Bytes(STR))

    // Byte Array Variable
    rule #packArgBy32(@tlll(_, LOC:Int, _), EXPR, %bytesT(L))
        => #packArgBy32BytesTVar(L, #compileExpr(EXPR), %bytesT(L))


    // List Literal
    rule #packArgBy32(@tlll(_, LOC:Int, _), %list(EXPRS), T)
        => #ifThen(#numOfExprs(EXPRS) =/=Int #getListTCount(T),
                   #exception("The length of list doesn't match the expected length."))
        ~> #packArgBy32ListTLiteral(LOC, EXPRS, T, .LLLExps, 0)
      requires isListType(T)

    // List Var
    rule #packArgBy32(@tlll(_, LOC:Int, _), EXPR, T)
        => #packArgBy32ListTVar(LOC, #compileExpr(EXPR), T, .LLLExps, 0, 0)
      requires isListType(T) andBool notBool(isListExpr(EXPR))


    syntax CPackedArgBy32  ::= "#packArgBy32Base"    "(" Int          ","  // packing loc
                                                         CTypedLLLExp ","
                                                         Type              // arg type
                                                     ")"      [strict(2)]

    syntax CPackedArgBy32  ::= "#packArgBy32BaseAux" "(" Int          ","
                                                         CTypedLLLExp ")"  [strict(2)]
 // ----------------------------------------------------------------------------------
    rule #packArgBy32Base(LOC, TCODE, ARGTYPE)
        => #packArgBy32BaseAux(LOC, #baseTypeConvert(TCODE, ARGTYPE))

    rule #packArgBy32BaseAux(LOC, @tlll(_, CODE, _)) => @argby32($mstore(LOC, CODE),.LLLExps, 32)


    syntax CPackedArgBy32  ::= "#packArgBy32StringLiteral" "(" Int    ","  // packing loc
                                                               CBytes ")"  [strict(2)]
 // ----------------------------------------------------------------------------------
    rule #packArgBy32StringLiteral(LOC, BS)
        => @argby32($mstore(LOC, #bytes2Int(BS, 32, 0)), 32)


    syntax CPackedArgBy32  ::= "#packArgBy32BytesTVar" "(" Int          ","  // packing loc
                                                           CTypedLLLExp ","
                                                           Type              // arg type
                                                       ")"      [strict(2)]
 // -----------------------------------------------------------------------
    // TODO: https://github.com/ethereum/viper/issues/551


    syntax CPackedArgBy32  ::= "#packArgBy32ListTLiteral" "(" Int     ","  // packing loc
                                                              Exprs   ","
                                                              Type    ","  // arg type
                                                              LLLExps ","  // result code
                                                              Int     ")"  // total size
 // ---------------------------------------------------------------------
    rule #packArgBy32ListTLiteral(LOC, .Exprs, T, RESULTCODE, TOTALSIZE)
        => @argby32(RESULTCODE, TOTALSIZE)

    rule #packArgBy32ListTLiteral(LOC, EXPR EXPRS, %listT(SUBTYPE, N), RESULTCODE, TOTALSIZE)
        => #packArgBy32(@tlll(SUBTYPE, LOC, @locattr(@memory, true)), EXPR, SUBTYPE)
        ~> #packArgBy32ListTLiteral(LOC, EXPRS, %listT(SUBTYPE, N), RESULTCODE, TOTALSIZE)

    rule @argby32(CODE, SIZE) ~> #packArgBy32ListTLiteral(LOC, EXPRS, T, RESULTCODE, TOTALSIZE)
        => #packArgBy32ListTLiteral(LOC +Int SIZE, EXPRS, T, RESULTCODE ++LLL CODE, TOTALSIZE +Int SIZE)


    syntax CPackedArgBy32  ::= "#packArgBy32ListTVar" "(" Int          ","  // packing loc
                                                          CTypedLLLExp ","
                                                          Type         ","  // arg type
                                                          LLLExps      ","  // result code
                                                          Int          ","  // index
                                                          Int          ")"  // total size
 // ----------------------------------------------------------------------
    // TODO: https://github.com/ethereum/viper/issues/551


    syntax CTypedLLLExp  ::= "#packLoggingTopic" "(" Expr "," EventParams ")"
 // -------------------------------------------------------------------------
    // Base Type
    rule #packLoggingTopic(ARG, %eparam(_, T, _)) => #packLoggingTopicBase(#compileExpr(ARG), T)
      requires isBaseType(T)

    // String Literal
    rule #packLoggingTopic(ARG, %eparam(_, %bytesT(L), _))
        => #ifThen(lengthString(ARG) >Int L,
                   #exception("Topic input bytes are to big."))
        ~> #packLoggingTopicStringLiteral(#string2Bytes(ARG), %bytesT(L))
      requires isString(ARG)

    // Byte Array Variable
    rule #packLoggingTopic(ARG, %eparam(_, %bytesT(L), _))
        => #packLoggingTopicBytesTVar(#compileExpr(ARG), %bytesT(L))
      requires notBool isString(ARG)



    syntax CTypedLLLExp  ::= "#packLoggingTopicBase" "(" CTypedLLLExp "," Type ")"  [strict(1)]
 // -------------------------------------------------------------------------------------------
    rule #packLoggingTopicBase(ARGCODE, T) => #baseTypeConvert(ARGCODE, T)


    syntax CTypedLLLExp  ::= "#packLoggingTopicStringLiteral" "(" CBytes "," Type ")"  [strict(1)]
 // ----------------------------------------------------------------------------------------------
    rule #packLoggingTopicStringLiteral(BS, %bytesT(L))
        => #ifThen(#numOfBytes(BS) >Int 32,
                   #exception("Can only log a maximum of 32 bytes at a time."))
        ~> @tlll(%bytesT(L), #bytes2Int(BS, 32, 0), @none)


    syntax CTypedLLLExp  ::= "#packLoggingTopicBytesTVar" "(" CTypedLLLExp "," Type ")"  [strict(1)]
 // ------------------------------------------------------------------------------------------------
    // TODO: https://github.com/ethereum/viper/issues/546


// Statement Expression
// ====================


    rule #compileStmt(%stmtexpr(EXPR)) => #stmtExpr(EXPR)


    syntax CLLLExps  ::= "#stmtExpr" "(" Expr ")"
 // ---------------------------------------------


    syntax CLLLExps  ::= "#icallNoReturn" "(" Exprs "," FuncRecord ")"
 // ----------------------------------------------------------------------
    rule <k> #stmtExpr(%icall(FNAME, ARGS)) => #icallNoReturn(ARGS, FUNCRECORD) ... </k>
         <internalSig> FNAME |-> FUNCRECORD SIGS </internalSig>

    // TODO: Is it necessary to enforce that functions cannot call functions defined later than themselves?
    rule <k> #stmtExpr(%icall(FNAME, _)) => #exception("Function not declared yet: " +String Id2String(FNAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool FNAME in_keys(SIGS)

    // EVM: CALL GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
    rule <k> #icallNoReturn(ARGS, @func(FUNCID, FNAME, PARAMS, RETT, _, _, _))
            => #ifThen(#numOfExprs(ARGS) =/=K #numOfParams(PARAMS),
                       #exception("# of args doesn't match # of params in function" +String Id2String(FNAME) +String
                                  " expected: " +String Int2String(#numOfParams(PARAMS)) +String
                                  ", actual: " +String Int2String(#numOfExprs(ARGS))))
            ~> #icallNoReturnAux(#packArguments(#compileExprs(ARGS), FUNCID, PARAMS))
         ... </k>


    syntax CLLLExps  ::= "#icallNoReturnAux" "(" CPackedArgData ")"  [strict]
 // -------------------------------------------------------------------------
    rule #icallNoReturnAux(@argdata(CODE, ARGSWIDTH))
        => $assert($call($gas, $address, 0, CODE, ARGSWIDTH, 0, 0)),.LLLExps


// Send
// ====


    rule <k> #compileStmt(%send(TO, VALUE))
            => #ifThenElse(CONSTANT ==K true,
                           #exception("Cannot send ether inside a constant function"),
                           #send(#compileValueExpr(TO), #compileValueExpr(VALUE))) ... </k>
         <constant> CONSTANT </constant>


    syntax CLLLExps  ::= "#send"    "(" CTypedLLLExp /*to*/ "," CTypedLLLExp /*value*/ ")"  [seqstrict]
    syntax CLLLExps  ::= "#sendAux" "(" TypedLLLExp "," TypedLLLExp ")"
 // ---------------------------------------------------------------------------------------------------
    rule #send(TTOCODE, @tlll(T, VALUECODE, EXPRATTR))
        => #sendAux(TTOCODE,
                    @tlll(#convertToUnitIfPure(T, @unittuple((%wei |-> 1), false)), VALUECODE, EXPRATTR))

    rule #sendAux(@tlll(%address, TOCODE, _), @tlll(%unitT(%num, %wei |-> 1, false), VALUECODE, _))
        => $assert($call(0, TOCODE, VALUECODE, 0, 0, 0, 0)),.LLLExps


// Selfdestruct
// ============


    rule <k> #compileStmt(%selfdestruct(ADDR))
            => #exception("Cannot self destruct inside a constant function! ")
         ... </k>
         <constant> true </constant>

    rule <k> #compileStmt(%selfdestruct(ADDR))
            => #selfdestruct(#compileValueExpr(ADDR))
         ... </k>
         <constant> false </constant>


    syntax CLLLExps  ::= "#selfdestruct" "(" CTypedLLLExp ")"  [strict]
 // -------------------------------------------------------------------
    rule #selfdestruct(@tlll(%address, ADDRCODE, _)) => $selfdestruct(ADDRCODE),.LLLExps



///////////////////////////////////////////////////////////////////////////////
// Expressions
///////////////////////////////////////////////////////////////////////////////


    syntax CTypedLLLExps  ::= "#compileExprs" "(" Exprs ")"
    syntax CTypedLLLExps  ::= "#compileExprsAux" "(" Exprs "," TypedLLLExps ")"
 // ---------------------------------------------------------------------------
    rule #compileExprs(EXPRS) => #compileExprsAux(EXPRS, .TypedLLLExps)

    rule #compileExprsAux(.Exprs, RESULTCODE) => RESULTCODE

    rule #compileExprsAux((EXPR EXPRS), RESULTCODE)
        => #compileExpr(EXPR)
        ~> #compileExprsAux(EXPRS, RESULTCODE)

    rule TCODE:TypedLLLExp ~> #compileExprsAux(EXPRS, RESULTCODE)
        => #compileExprsAux(EXPRS, RESULTCODE ++TLLL (TCODE .TypedLLLExps))


    // Compile an expression that results in a value
    syntax CTypedLLLExp  ::= "#compileValueExpr"    "(" Expr ")"
    syntax CTypedLLLExp  ::= "#compileValueExprAux" "(" CTypedLLLExp ")"  [strict]
 // ------------------------------------------------------------------------------
    rule #compileValueExpr(EXPR) => #compileValueExprAux(#compileExpr(EXPR))

    rule #compileValueExprAux(TCODE) => #unwrapLoc(TCODE)


    // Compile an expression that represents an address in memory or storage
    syntax CTypedLLLExp  ::= "#compileLocExpr"    "(" Expr ")"
    syntax CTypedLLLExp  ::= "#compileLocExprAux" "(" CTypedLLLExp ")"  [strict]
 // ----------------------------------------------------------------------------
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


// String Literal
// ===============


    rule #compileExpr(STR:String) => #string(#string2Bytes(STR))


    syntax CTypedLLLExp  ::= "#string"    "(" CBytes ")"  [strict(1)]

    syntax CTypedLLLExp  ::= "#stringAux" "(" CTypedLLLExp ","  // placeholder
                                              Bytes        ","
                                              Int               // bytes length
                                          ")"             [strict(1)]
 // -----------------------------------------------------------------
    rule #string(BS)
        => #stringAux(#newPlaceholder(%bytesT(#numOfBytes(BS))), BS, #numOfBytes(BS))

    rule #stringAux(@tlll(T, LOC, LOCATTR), BS, LEN)
        => #encodeBytes(@tlll(T, LOC, LOCATTR), BS, LEN, 32, $mstore(LOC, LEN),.LLLExps)


    syntax CTypedLLLExp  ::= "#encodeBytes" "(" TypedLLLExp  ","  // placeholder
                                                Bytes        ","
                                                Int          ","  // bytes length
                                                Int          ","  // offset
                                                LLLExps      ")"
 // ------------------------------------------------------------
    rule #encodeBytes(@tlll(T, LOC, _), .Bytes, 0, _, RESULTCODE)
        => @tlll(T, $%seq(RESULTCODE ++LLL (LOC,.LLLExps)), @locattr(@memory, true))

    rule #encodeBytes(@tlll(T, LOC, LOCATTR), BS, LEN, OFFSET, RESULTCODE)
        => #encodeBytes(@tlll(T, LOC, LOCATTR),
                        .Bytes,
                        0,
                        OFFSET +Int 32,
                        RESULTCODE ++LLL ($mstore(
                                            $add(LOC, OFFSET),
                                            #bytes2Int(BS, 32, 0)),.LLLExps))
      requires LEN >Int 0 andBool LEN <=Int 32

    rule #encodeBytes(@tlll(T, LOC,LOCATTR), BS, LEN, OFFSET, RESULTCODE)
        => #encodeBytes(@tlll(T, LOC, LOCATTR),
                        #drop(32, BS),
                        LEN -Int 32,
                        OFFSET +Int 32,
                        RESULTCODE ++LLL ($mstore(
                                            $add(LOC, OFFSET),
                                            #bytes2Int(#take(32, BS), 32, 0)),.LLLExps))
      requires LEN >Int 32


// Bool
// ====


    rule #compileExpr(true)  => @tlll(%bool, 1, @none)

    rule #compileExpr(false)  => @tlll(%bool, 0, @none)


// Variable
// ========


    rule #compileExpr(%self) => @tlll(%address, $address, @none)

    rule #compileExpr(V) => #lookupVar(V)


// List Literal
// =============


    rule #compileExpr(%list(EXPRS)) => #listLiteral(EXPRS)
      requires #numOfExprs(EXPRS) >Int 0

    rule #compileExpr(%list(EXPRS)) => #exception("List must have elements")
      requires #numOfExprs(EXPRS) ==Int 0


    // Additional LLLExp to handle lists
    syntax MultiLLLExp  ::= "$multi" "(" TypedLLLExps ")"
    syntax LLLExp       ::= MultiLLLExp
 // ------------------------------------------------


    syntax CTypedLLLExp  ::= "#listLiteral" "(" Exprs ")"
 // ------------------------------------------------------
    rule #listLiteral(EXPR EXPRS) => #processListLiteralFirstElem(EXPR)
                                  ~> #processListLiteralRestElems(EXPRS, .TypedLLLExps)


    syntax CTypedLLLExp  ::= "#processListLiteralFirstElem" "(" Expr ")"
 // ----------------------------------------------------------------------
    rule #processListLiteralFirstElem(EXPR) => #compileExpr(EXPR)


    syntax CTypedLLLExp  ::= "#processListLiteralRestElems"    "(" Exprs "," TypedLLLExps ")"
    syntax CTypedLLLExp  ::= "#processListLiteralRestElemsAux" "(" Type "," Int "," Exprs "," TypedLLLExps ")"
 // -----------------------------------------------------------------------------------------------------------
    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralRestElems(EXPRS, .TypedLLLExps)
        => #processListLiteralRestElemsAux(T, 1, EXPRS, @tlll(T, CODE, EXPRATTR) .TypedLLLExps)

    rule #processListLiteralRestElemsAux(T, LEN, .Exprs, RESULTCODE)
        => @tlll(%listT(T, LEN), $multi(RESULTCODE), @none)

    rule #processListLiteralRestElemsAux(T, LEN, (EXPR EXPRS), RESULTCODE)
        => #compileExpr(EXPR) ~> #processListLiteralRestElemsAux(T, LEN, EXPRS, RESULTCODE)

    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralRestElemsAux(T, LEN, EXPRS, RESULTCODE)
        => #processListLiteralRestElemsAux(T, LEN +Int 1, EXPRS,
                                           RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))

    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralRestElemsAux(ELEMT, LEN, EXPRS, RESULTCODE)
        => #processListLiteralRestElemsAux(%mixedT, LEN +Int 1, EXPRS,
                                           RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))
      requires T =/=K ELEMT


// Struct Literal
// ===============


    rule #compileExpr(%struct(ITEMS)) => #structLiteral(ITEMS, .Ids, .AnnVars, .TypedLLLExps)


    syntax CTypedLLLExp  ::= "#structLiteral" "(" StructItems  ","
                                                  Ids          ","  // names of the fields (for name duplication check)
                                                  AnnVars      ","  // struct fields (for inferring struct type)
                                                  TypedLLLExps ")"  // result code

    syntax KItem  ::= "#nameWithValue" "(" Id "," CTypedLLLExp ")"    [strict(2)]
 // -----------------------------------------------------------------------------
    rule #structLiteral(.StructItems, NAMES, ANNVARS, RESULTCODE)
        => @tlll(%structT(ANNVARS), $multi(RESULTCODE), @none)

    rule #structLiteral(%item(NAME, EXPR) ITEMS, NAMES, ANNVARS, RESULTCODE)
        => #ifThen(notBool #isVarNameValid(NAME),
                   #exception("Invalid member variable for struct."))
        ~> #ifThen(#inIds(NAME, NAMES),
                   #exception("Member variable duplicated: " +String Id2String(NAME)))
        ~> #nameWithValue(NAME, #compileExpr(EXPR))
        ~> #structLiteral(ITEMS, NAMES, ANNVARS, RESULTCODE)

    rule #nameWithValue(NAME, @tlll(T, CODE, EXPRATTR)) ~> #structLiteral(ITEMS, NAMES, ANNVARS, RESULTCODE)
        => #structLiteral(ITEMS, NAMES ++Id (NAME .Ids),
                          ANNVARS ++Annvar (%annvar(NAME, T) .AnnVars),
                          RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))


// Arithmetic
// ==========


    rule #compileExpr(%binop(BOP, LEXPR, REXPR))
        => #binOp(BOP, #compileValueExpr(LEXPR), #compileValueExpr(REXPR))


    syntax CTypedLLLExp  ::= "#binOp" "(" BinOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
 // ---------------------------------------------------------------------------------------------------
    rule #binOp(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
                   #exception("Unsupported types for arithmetic op"))
        ~> #ifThenElse(isPureNumType(LT) andBool isPureNumType(RT),
                       #binOpPure(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR)),
                       #binOpMix(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR)))


    syntax CTypedLLLExp  ::= "#binOpMix" "(" BinOp "," TypedLLLExp "," TypedLLLExp ")"
    syntax CTypedLLLExp  ::= "#binOpMixAux" "(" K "," CTypedLLLExp ")"    [seqstrict]
 // ----------------------------------------------------------------------------------
    rule #binOpMix(BOP, @tlll(LT:NumericType, LCODE, LEXPRATTR), @tlll(RT:NumericType, RCODE, REXPRATTR))
        => #binOpMixAux(#newUnitTuple(BOP, LT, RT, RCODE),
                        #binOpPure(BOP,
                                   @tlll(#dropUnit(LT), LCODE, LEXPRATTR),
                                   @tlll(#dropUnit(RT), RCODE, REXPRATTR)))

    rule #binOpMixAux(@unittuple(UNITMAP, POSITIONAL), @tlll(T, TCODE, EXPRATTR))
        => @tlll(%unitT(T, UNITMAP, POSITIONAL), TCODE, EXPRATTR)


    syntax UnitTuple  ::= "@unittuple" "(" Map "," Bool ")"
    syntax KItem      ::= "#newUnitTuple" "(" BinOp "," Type "," Type "," LLLExp ")"
 // --------------------------------------------------------------------------------
   // add
   rule #newUnitTuple(+, %unitT(_, LM:Map, LPOS), %unitT(_, RM:Map, RPOS), _)
        => #ifThen(LM =/=K RM,
                   #exception("Unit mismatch."))
        ~> #ifThen(LPOS ==K true andBool RPOS ==K true,
                   #exception("Cannot add two positional units!"))
        ~> @unittuple(LM, LPOS xorBool RPOS)

    rule #newUnitTuple(+, %unitT(LT, LM:Map, LPOS), RT:PureNumType, _)
        => @unittuple(LM, LPOS)

    rule #newUnitTuple(+, LT:PureNumType, %unitT(RT, RM:Map, RPOS), _)
        => @unittuple(RM, RPOS)

    // subtract
    rule #newUnitTuple(-, %unitT(_, LM:Map, LPOS), %unitT(_, RM:Map, RPOS), _)
        => #ifThen(LM =/=K RM,
                   #exception("Unit mismatch."))
        ~> @unittuple(LM, LPOS xorBool RPOS)

    rule #newUnitTuple(-, %unitT(LT, LM:Map, LPOS), RT:PureNumType, _)
        => @unittuple(LM, LPOS)

    rule #newUnitTuple(-, LT:PureNumType, %unitT(RT, RM:Map, RPOS), _)
        => @unittuple(RM, RPOS)

    // multiply
    rule #newUnitTuple(*, %unitT(_, LM:Map, LPOS), %unitT(_, RM:Map, RPOS), _)
        => #ifThen(LPOS ==K true orBool RPOS ==K true,
                   #exception("Cannot multiply positional values!"))
        ~> @unittuple(#combineUnits(LM, RM, false), false)

    rule #newUnitTuple(*, %unitT(LT, LM:Map, LPOS), RT:PureNumType, _)
        => #ifThen(LPOS ==K true,
                   #exception("Cannot multiply positional values!"))
        ~> @unittuple(LM, false)

    rule #newUnitTuple(*, LT:PureNumType, %unitT(RT, RM:Map, RPOS), _)
        => #ifThen(RPOS ==K true,
                   #exception("Cannot multiply positional values!"))
        ~> @unittuple(RM, false)

    // divide
    rule #newUnitTuple(/, %unitT(_, LM:Map, LPOS), %unitT(_, RM:Map, RPOS), _)
        => #ifThen(LPOS ==K true orBool RPOS ==K true,
                   #exception("Cannot divide positional values!"))
        ~> @unittuple(#combineUnits(LM, RM, true), false)

    rule #newUnitTuple(/, %unitT(LT, LM:Map, LPOS), RT:PureNumType, _)
        => #ifThen(LPOS ==K true,
                   #exception("Cannot divide positional values!"))
        ~> @unittuple(LM, false)

    rule #newUnitTuple(/, LT:PureNumType, %unitT(RT, RM:Map, RPOS), _)
        => #ifThen(RPOS ==K true,
                   #exception("Cannot divide positional values!"))
        ~> @unittuple(#combineUnits(.Map, RM, true), false)

    // mod
    rule #newUnitTuple(%, %unitT(_, LM:Map, LPOS), %unitT(_, RM:Map, RPOS), _)
        => #ifThen(LPOS ==K true orBool RPOS ==K true,
                   #exception("Cannot use positional values as modulus arguments!"))
        ~> #ifThen(LM =/=K RM,
                   #exception("Modulus arguments must have same unit."))
        ~> @unittuple(LM, false)

    rule #newUnitTuple(%, %unitT(LT, LM:Map, LPOS), RT:PureNumType, _)
        => #ifThen(LPOS ==K true,
                   #exception("Cannot use positional values as modulus arguments!"))
        ~> @unittuple(LM, false)

    rule #newUnitTuple(%, LT:PureNumType, %unitT(RT, RM:Map, RPOS), _)
        => #ifThen(RPOS ==K true,
                   #exception("Cannot use positional values as modulus arguments!"))
        ~> @unittuple(RM, false)

    // exp
    rule #newUnitTuple(%, %unitT(_, LM:Map, LPOS), %unitT(_, RM:Map, RPOS), _)
        => #exception("Cannot use unit values as exponential arguments!")

    rule #newUnitTuple(%, %unitT(LT, LM:Map, LPOS), RT:PureNumType, POW:Int)
        ~> @unittuple(#computeUnitPow(LM, POW), false)

    rule #newUnitTuple(%, %unitT(LT, LM:Map, LPOS), RT:PureNumType, CODE)
        ~> #exception("The exponent of a unit value must be integer.")
      requires notBool isInt(CODE)

    rule #newUnitTuple(%, LT:PureNumType, %unitT(RT, RM:Map, RPOS), _)
        => #exception("Cannot use unit values as exponential arguments!")


    syntax CTypedLLLExp  ::= "#binOpPure"    "(" BinOp "," TypedLLLExp "," TypedLLLExp ")"
    syntax CTypedLLLExp  ::= "#binOpPureAux" "(" BinOp "," TypedLLLExp "," TypedLLLExp ")"
 // --------------------------------------------------------------------------------------
    rule #binOpPure(BOP, LTCODE, RTCODE)
        => #binOpPureAux(BOP, LTCODE, RTCODE)
        ~> #clampArithResult

    rule #binOpPureAux(+, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $add(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                         @tlll(%decimal, $add($mul(LCODE, @decimalDivisor), RCODE), @none),
               #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                           @tlll(%decimal, $add(LCODE, $mul(RCODE, @decimalDivisor)), @none),
                           #exception("How did I get here?"))))

    rule #binOpPureAux(-, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $sub(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                         @tlll(%decimal, $sub($mul(LCODE, @decimalDivisor), RCODE), @none),
               #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                           @tlll(%decimal, $sub(LCODE, $mul(RCODE, @decimalDivisor)), @none),
                           #exception("How did I get here?"))))

    rule #binOpPureAux(*, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT andBool LT ==K %num,
                       @tlll(%num, $mul(LCODE, RCODE), @none),
             #ifThenElse(LT ==K RT andBool LT ==K %decimal,
                         @tlll(%decimal, $with($r, RCODE,
                                           $with($l, LCODE,
                                             $with($ans, $mul($l, $r),
                                               $%seq(
                                                 $assert($or($eq($sdiv($ans, $l), $r), $not($l))),
                                                 $sdiv($ans, @decimalDivisor),.LLLExps)))), @none),
               #ifThen((LT ==K %num andBool RT ==K %decimal) orBool (LT ==K %decimal andBool RT ==K %num),
                       @tlll(%decimal, $with($r, RCODE,
                                         $with($l, LCODE,
                                           $with($ans, $mul($l, $r),
                                             $%seq(
                                               $assert($or($eq($sdiv($ans, $l), $r), $not($l))),
                                               $ans,.LLLExps)))), @none))))

    rule #binOpPureAux(/, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(RT ==K %num,
                       @tlll(LT, $sdiv(LCODE, $clamp_nonzero(RCODE)), @none),
             #ifThenElse(LT ==K RT andBool LT ==K %decimal,
                         @tlll(%decimal, $with($l, LCODE,
                                           $with($r, $clamp_nonzero(RCODE),
                                             $sdiv($mul($l, @decimalDivisor), $r))), @none),
               #ifThen(LT ==K %num andBool RT ==K %decimal,
                       @tlll(%decimal,
                             $sdiv($mul(LCODE, @decimalDivisor ^Int 2), $clamp_nonzero(RCODE)), @none))))

    rule #binOpPureAux(%, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $smod(LCODE, $clamp_nonzero(RCODE)), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%decimal, $smod(LCODE, $mul($clamp_nonzero(RCODE), @decimalDivisor)), @none),
               #ifThen(LT ==K %num andBool RT ==K %decimal,
                       @tlll(%decimal, $smod($mul(LCODE, @decimalDivisor), $clamp_nonzero(RCODE)), @none))))

    rule #binOpPureAux(**, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
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
        => #compareOp(COP, #compileExpr(LEXP), #compileExpr(REXP))


    syntax CTypedLLLExp  ::= "#compareOp" "(" CompareOp    ","
                                              CTypedLLLExp ","
                                              CTypedLLLExp
                                          ")"  [seqstrict(2,3)]
 // -----------------------------------------------------------
    rule #compareOp(%in, @tlll(LT, LCODE, LEXPRATTR), @tlll(%listT(SUBTYPE, N), RCODE, REXPRATTR))
        => #ifThen(notBool(#areUnitsCompatible(LT, SUBTYPE, #isNumLiteral(LCODE))) andBool
                   notBool(#areUnitsCompatible(SUBTYPE, LT, #isNumLiteral(RCODE))),
                   #exception("Can't use IN comparison with different types!"))
        ~> #buildInComparator(@tlll(LT, LCODE, LEXPRATTR),
                              @tlll(%listT(SUBTYPE, N), RCODE, REXPRATTR),
                              #newPlaceholder(%bool))

    rule #compareOp(COP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(notBool(#areUnitsCompatible(LT, RT, #isNumLiteral(LCODE))) andBool
                   notBool(#areUnitsCompatible(RT, LT, #isNumLiteral(RCODE))),
                   #exception("Can't compare values with different units!"))
        ~> #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
             #ifThen(COP =/=K %eq andBool COP =/=K %ne,
                     #exception("Invalid type for comparison op")))
        ~> #compareOpAux(COP,
                         #unwrapLoc(@tlll(#dropUnit(LT), LCODE, LEXPRATTR)),
                         #unwrapLoc(@tlll(#dropUnit(RT), RCODE, REXPRATTR)))
      requires COP =/=K %in


    // in comparator
    // TODO: https://github.com/ethereum/viper/issues/581
    //       https://github.com/ethereum/viper/issues/582
    //       Need to think carefully how to implement list and type casting.
    syntax CTypedLLLExp  ::= "#buildInComparator" "(" TypedLLLExp  ","  // left
                                                      TypedLLLExp  ","  // right
                                                      CTypedLLLExp      // result placeholder
                                                  ")"      [strict(3)]

    syntax CTypedLLLExp  ::= "#buildInComparatorAux" "(" CLLLExps ")"  [strict]
 // ---------------------------------------------------------------------------
    rule #buildInComparator(TLCODE, TRCODE, @tlll(_, RESULTLOC, _))
        => #buildInComparatorAux(#compareSeq(TLCODE, TRCODE, RESULTLOC))

    rule #buildInComparatorAux(COMPARESEQ) => @tlll(%bool, $eq(1, COMPARESEQ), @none)


    syntax CLLLExps  ::= "#compareSeq" "(" TypedLLLExp "," TypedLLLExp "," Int ")"

    syntax CLLLExps  ::= "#compareSeqAux" "(" LLLExps  ","  // setter
                                              CLLLExps      // for_loop_seq
                                          ")"  [strict(2)]
 // --------------------------------------------------------------------------------------
    rule #compareSeq(TLCODE, @tlll(RT, RCODE, EXPRATTR), RESULTLOC)
        => #compareSeqListTLiteral(TLCODE, @tlll(RT, RCODE, EXPRATTR), RESULTLOC,
                                   #newPlaceholder(RT))
      requires isMultiLLLExp(RCODE)

    rule #compareSeq(TLCODE, @tlll(RT, RCODE, EXPRATTR), RESULTLOC)
        => #compareSeqListTVar(TLCODE, @tlll(RT, RCODE, EXPRATTR), RESULTLOC)
      requires notBool isMultiLLLExp(RCODE)

    rule #compareSeqAux(SETTER, FORLOOPSEQ) => $%seq(SETTER ++LLL FORLOOPSEQ),.LLLExps


    syntax CLLLExps  ::= "#compareSeqListTLiteral" "(" TypedLLLExp  ","
                                                       TypedLLLExp  ","
                                                       Int          ","  // result loc
                                                       CTypedLLLExp      // tmp_list
                                                   ")"      [strict(3)]

    syntax CLLLExps  ::= "#compareSeqListTLiteralAux" "(" TypedLLLExp ","
                                                          TypedLLLExp ","
                                                          Int         ","  // result loc
                                                          CLLLExps    ","  // setter
                                                          LLLExp           // load_i_from_list
                                                      ")"      [strict(4)]
 // ----------------------------------------------------------------------
    rule #compareSeqListLiteral(TLCODE, TRCODE, RESULTLOC, @tlll(T, TMPLISTLOC, LOCATTR))
        => #compareSeqListTLiteralAux(TLCODE, TRCODE, RESULTLOC,
                                      #mkSetter(@tlll(T, TMPLISTLOC, LOCATTR), TRCODE),
                                      $mload(add(TMPLISTLOC, $mul(32, $mload(@freeLoopIndexPos)))))

    rule #compareSeqListTLiteralAux(TLCODE, TRCODE, RESULTLOC, SETTER, LODEFROMLIST)
        => #compareSeqAux(SETTER, .LLLExps)



    // normal compare operator
    syntax CTypedLLLExp  ::= "#compareOpAux" "(" CompareOp "," TypedLLLExp  "," TypedLLLExp ")"
 // -------------------------------------------------------------------------------------------
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


    syntax CTypedLLLExp  ::= "#icallWithReturn" "(" Exprs "," FuncRecord ")"
 // ------------------------------------------------------------------------
    rule <k> #compileExpr(%icall(FNAME, ARGS)) => #icallWithReturn(ARGS, FUNCRECORD) ... </k>
         <internalSig> FNAME |-> FUNCRECORD SIGS </internalSig>

    // TODO: Is it necessary to enforce that functions cannot call functions defined later than themselves?
    rule <k> #compileExpr(%icall(FNAME, _)) => #exception("Function not declared yet: " +String Id2String(FNAME)) ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool FNAME in_keys(SIGS)

    // EVM: CALL GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
    rule <k> #icallWithReturn(ARGS, @func(FUNCID, FNAME, PARAMS, RETT, _, _, _))
            => #ifThen(#numOfExprs(ARGS) =/=K #numOfParams(PARAMS),
                       #exception("# of args doesn't match # of params in function" +String Id2String(FNAME) +String
                                  " expected: " +String Int2String(#numOfParams(PARAMS)) +String
                                  ", actual: " +String Int2String(#numOfExprs(ARGS))))
            ~> #ifThen(RETT ==K %void,
                       #exception("expect a value, but the function doesn't return a value."))
            ~> #icallWithReturnAux(#packArguments(#compileExprs(ARGS), FUNCID, PARAMS),
                                   #newPlaceholder(RETT),
                                   #sizeOfType(RETT))
         ... </k>


    syntax CTypedLLLExp  ::= "#icallWithReturnAux" "(" CPackedArgData ","  // packed args
                                                       CTypedLLLExp   ","  // return start
                                                       Int                 // return width
                                                   ")"  [seqstrict(1, 2)]
 // ---------------------------------------------------------------------
    // Base
    rule #icallWithReturnAux(PACKEDARGS, @tlll(RETT, LOC, LOCATTR), RETWIDTH)
        => #icallWithReturner(PACKEDARGS, @tlll(RETT, LOC, LOCATTR), RETWIDTH, LOC)
      requires isBaseType(RETT)

    // Byte Array
    rule #icallWithReturnAux(PACKEDARGS, @tlll(RETT, LOC, LOCATTR), RETWIDTH)
        => #icallWithReturner(PACKEDARGS, @tlll(RETT, LOC, LOCATTR), RETWIDTH, LOC +Int 32)
      requires isByteArrayType(RETT)


    // TODO: List?


    syntax CTypedLLLExp  ::= "#icallWithReturner" "(" PackedArgData ","  // packed args
                                                      TypedLLLExp   ","  // return start
                                                      Int           ","  // return width
                                                      Int           ")"  // returner
 // -------------------------------------------------------------------
    rule #icallWithReturner(@argdata(CODE, ARGSWIDTH), @tlll(RETT, LOC, LOCATTR), RETWIDTH, RETURNER)
        => @tlll(RETT, $%seq(
                         $assert($call($gas, $address, 0, CODE, ARGSWIDTH, LOC, RETWIDTH)),
                         RETURNER,.LLLExps), @locattr(@memory, true))


    syntax CPackedArgData  ::= "#packArguments"    "(" CTypedLLLExps ","  // typed args code
                                                       Int           ","  // func id
                                                       Params             // params
                                                   ")"       [strict(1)]
 // -------------------------------------------------------------------
    rule #packArguments(TARGS:TypedLLLExps, FUNCID, PARAMS)
        => #allocMemForPackedArgs(TARGS,
                                  #newPlaceholder(%bytesT(#sizeOfPackedArgs(TARGS) +Int 32)),
                                  FUNCID, PARAMS)


    syntax CPackedArgData  ::= "#allocMemForPackedArgs" "(" TypedLLLExps ","  // typed args code
                                                            CTypedLLLExp ","  // placeholder
                                                            Int          ","  // func id
                                                            Params            // params
                                                        ")"      [strict(2)]
 // ------------------------------------------------------------------------
    rule #allocMemForPackedArgs(TARGS, @tlll(T, LOC, _), FUNCID, PARAMS)
        => #packArgumentsAux(LOC +Int 32, TARGS, PARAMS, #numOfTypedLLLExps(TARGS), ($mstore(LOC, FUNCID),.LLLExps),
                             LOC +Int 28, #sizeOfPackedArgs(TARGS) +Int 4, false)


    syntax CPackedArgData  ::= "#packArgumentsAux" "(" Int          ","  // packing loc for the first arg
                                                       TypedLLLExps ","  // typed args code
                                                       Params       ","  // params
                                                       Int          ","  // num of args
                                                       LLLExps      ","  // setter code
                                                       Int          ","  // start of the arg block (including the funcid)
                                                       Int          ","  // packed args width
                                                       Bool         ")"  // need pos?
 // -------------------------------------------------------------------
    rule #packArgumentsAux(_, .TypedLLLExps, .Params, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, false)
        => @argdata($%seq(SETTER ++LLL (ARGSSTART,.LLLExps)), ARGSWIDTH)

    rule #packArgumentsAux(_, .TypedLLLExps, .Params, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, true)
        => @argdata($with($_poz, ARGNUM *Int 32,
                      $%seq(SETTER ++LLL (ARGSSTART,.LLLExps))), ARGSWIDTH)

    // Base Type
    rule #packArgumentsAux(ARGLOC, (TARG TARGS), (%param(_, T) PARAMS), ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, NEEDPOS)
        => #packArgumentBase(@tlll(T, ARGLOC, @locattr(@memory, true)), TARG)
        ~> #packArgumentsAux(ARGLOC, TARGS, PARAMS, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, NEEDPOS)
      requires isBaseType(T)

    // Byte Array Type
    // TODO: Byte Array packing does not comply with ABI specification?
    rule #packArgumentsAux(ARGLOC, (TARG TARGS), (%param(_, T) PARAMS), ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, NEEDPOS)
        => #packArgumentBytesT(@tlll(T, ARGLOC, @locattr(@memory, true)), TARG, ARGSSTART +Int 4)
        ~> #packArgumentsAux(ARGLOC, TARGS, PARAMS, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, true)
      requires isByteArrayType(T)


    rule CODE:LLLExps ~> #packArgumentsAux(ARGLOC, TARGS, PARAMS, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, NEEDPOS)
        => #packArgumentsAux(ARGLOC +Int 32, TARGS, PARAMS, ARGNUM, SETTER ++LLL CODE, ARGSSTART, ARGSWIDTH, NEEDPOS)


    syntax CLLLExps  ::= "#packArgumentBase" "(" TypedLLLExp  ","  // typed arg loc
                                                 TypedLLLExp  ")"  // typed arg value
 // -------------------------------------------------------------
    rule #packArgumentBase(@tlll(PARAMT, LOC, LOCATTR), TARGCODE)
        => #mkSetter(@tlll(PARAMT, LOC, LOCATTR), TARGCODE)


    syntax CLLLExps  ::= "#packArgumentBytesT" "(" TypedLLLExp  ","  // typed arg loc
                                                   TypedLLLExp  ","  // typed arg value
                                                   Int          ")"  // start of the arg block (excluding the func id)

    syntax CLLLExps  ::= "#packArgumentBytesTAux" "(" TypedLLLExp ","  // arg copy
                                                      TypedLLLExp ","  // target
                                                      LLLExps     ","  // setter
                                                      LLLExp      ")"  // arg code
 // ---------------------------------------------------------------
    rule #packArgumentBytesT(@tlll(PARAMT, LOC, LOCATTR), @tlll(ARGT, ARGCODE, EXPRATTR), ARGBLOCKSTART)
        => #ifThen(notBool isByteArrayType(ARGT),
                   #exception("Arg expects byte array type but actual type is not."))
        ~> #packArgumentBytesTAux(@tlll(ARGT, $_s, EXPRATTR),
                                  @tlll(PARAMT, $add(ARGBLOCKSTART, $_poz), @locattr(@memory, true)),
                                  ($mstore(LOC, $_poz),.LLLExps),
                                  ARGCODE)

    rule #packArgumentBytesTAux(ARGCOPY, TARGET, SETTER, ARGCODE)
        => #packArgumentBytesTByCopy(#mkByteArrayCopier(TARGET, ARGCOPY),
                                     #getLength(ARGCOPY),
                                     SETTER, ARGCODE)


    syntax CLLLExps  ::= "#packArgumentBytesTByCopy" "(" CLLLExps     ","  // copier
                                                         CTypedLLLExp ","  // get length
                                                         LLLExps      ","  // setter
                                                         LLLExp            // arg code
                                                     ")"  [seqstrict(1,2)]
 // ----------------------------------------------------------------------
    rule #packArgumentBytesTByCopy(COPIER, @tlll(_, GETLENGTH, _), SETTER, ARGCODE)
        => SETTER ++LLL ($with($_s, ARGCODE,
                           $%seq(COPIER ++LLL
                                 ($set($_poz, $add(32, $add($_poz, GETLENGTH))),.LLLExps))),.LLLExps)


// Reserved Expr
// =============


    rule #compileExpr(%balance(EXPR))    => #balance(#compileValueExpr(EXPR))

    syntax CTypedLLLExp  ::= "#balance" "(" CTypedLLLExp ")"  [strict]
 // ------------------------------------------------------------------
    rule #balance(@tlll(%address, ADDR, @none)) => @tlll(%unitT(%num, %wei |-> 1, false), $balance(ADDR), @none)


    rule #compileExpr(%codesize(EXPR))   => #codesize(#compileValueExpr(EXPR))

    syntax CTypedLLLExp  ::= "#codesize" "(" CTypedLLLExp ")"   [strict]
 // --------------------------------------------------------------------
    rule #codesize(@tlll(%address, ADDR, @none)) => @tlll(%num, $extcodesize(ADDR), @none)


    rule #compileExpr(%is_contract(EXPR)) => #is_contract(#compileValueExpr(EXPR))

    syntax CTypedLLLExp  ::= "#is_contract" "(" CTypedLLLExp ")"  [strict]
 // ----------------------------------------------------------------------
    rule #is_contract(@tlll(%address, ADDR, @none)) => @tlll(%bool, $extcodesize(ADDR), @none)


    rule #compileExpr(%msg.sender)       => @tlll(%address, $caller, @none)

    rule #compileExpr(%msg.value)        => @tlll(%unitT(%num, %wei |-> 1, false), $callvalue, @none)

    rule #compileExpr(%msg.gas)          => @tlll(%num, $gas, @none)

    rule #compileExpr(%block.difficulty) => @tlll(%num, $difficulty, @none)

    rule #compileExpr(%block.timestamp)  => @tlll(%unitT(%num, %sec |-> 1, true), $timestamp, @none)

    rule #compileExpr(%block.coinbase)   => @tlll(%address, $coinbase, @none)

    rule #compileExpr(%block.number)     => @tlll(%num, $number, @none)

    rule #compileExpr(%block.prevhash)   => @tlll(%bytes32, $blockhash($sub($number, 1)), @none)

    rule #compileExpr(%tx.origin)        => @tlll(%address, $origin, @none)


// Reserved Function
// =================


    // floor
    syntax CTypedLLLExp  ::= "#floor" "(" CTypedLLLExp ")"    [strict]
 // ------------------------------------------------------------------
    rule #compileExpr(%floor(EXPR)) => #floor(#compileValueExpr(EXPR))

    rule #floor(@tlll(%decimal, CODE, EXPRATTR))
        => @tlll(%num, $sdiv(CODE, @decimalDivisor), EXPRATTR)

    rule #floor(@tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, EXPRATTR))
        => @tlll(%unitT(%num, UNITMAP, POSITIONAL), $sdiv(CODE, @decimalDivisor), EXPRATTR)


    // decimal
    syntax CTypedLLLExp  ::= "#decimal" "(" CTypedLLLExp ")"    [strict]
 // --------------------------------------------------------------------
    rule #compileExpr(%decimal(EXPR)) => #decimal(#compileValueExpr(EXPR))

    rule #decimal(@tlll(%num, CODE, _))
        => @tlll(%decimal, $mul(CODE, @decimalDivisor), @none)

    rule #decimal(@tlll(%unitT(%num, UNITMAP:Map, POSITIONAL), CODE, _))
        => @tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), $mul(CODE, @decimalDivisor), @none)

    rule #decimal(@tlll(%decimal, CODE, _))
        => @tlll(%decimal, CODE, @none)

    rule #decimal(@tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, _))
        => @tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, @none)


    // as_unitless_number
    syntax CTypedLLLExp  ::= "#asUnitlessNumber" "(" CTypedLLLExp ")"  [strict]
 // ---------------------------------------------------------------------------
    rule #compileExpr(%as_unitless_number(EXPR)) => #asUnitlessNumber(#compileValueExpr(EXPR))

    rule #asUnitlessNumber(@tlll(%num, CODE, _)) => @tlll(%num, CODE, @none)

    rule #asUnitlessNumber(@tlll(%unitT(%num, UNITMAP:Map, POSITIONAL), CODE, _))
        => @tlll(%num, CODE, @none)

    rule #asUnitlessNumber(@tlll(%decimal, CODE, _)) => @tlll(%decimal, CODE, @none)

    rule #asUnitlessNumber(@tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, _))
        => @tlll(%decimal, CODE, @none)


    // as_num128
    syntax CTypedLLLExp  ::= "#asNum128"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp  ::= "#asNum128Aux" "(" LLLExp ")"
 // ------------------------------------------------------------------------
    rule #compileExpr(%as_num128(EXPR)) => #asNum128(#compileValueExpr(EXPR))

    rule #asNum128(@tlll(T, CODE, _))
        => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %num256) orBool #isTypeOf(T, %address),
                       #asNum128Aux(CODE),
                       #exception("Function arg type does not match expected type."))

    rule #asNum128Aux(CODE) => @tlll(%num, $clamp($mload(@minNumPos), CODE, $mload(@maxNumPos)), @none)


    // as_num256
    syntax CTypedLLLExp  ::= "#asNum256"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp  ::= "#asNum256Aux" "(" TypedLLLExp ")"
 // ------------------------------------------------------------------------
    rule #compileExpr(%as_num256(EXPR)) => #asNum256(#compileValueExpr(EXPR))

    rule #asNum256(@tlll(T, CODE, EXPRATTR))
        => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %address),
                       #asNum256Aux(@tlll(T, CODE, EXPRATTR)),
                       #exception("Function arg type does not match expected type."))

    rule #asNum256Aux(@tlll(T, CODE, EXPRATTR))
        => #ifThenElse(isInt(CODE),
                       #asNum256Number(CODE),
                       #asNum256LLLExp(CODE))


    syntax CTypedLLLExp  ::= "#asNum256Number" "(" LLLExp ")"
    syntax CTypedLLLExp  ::= "#asNum256LLLExp" "(" LLLExp ")"
 // ---------------------------------------------------------
    rule #asNum256Number(I:Int) => #ifThenElse((I >=Int 0) andBool (I <=Int 2^Int 256 -Int 1),
                                               @tlll(%num256, I, @none),
                                               #exception("Number out of range"))

    rule #asNum256LLLExp(CODE) => @tlll(%num256, $clampge(CODE, 0), @none)


    // as_bytes32
    syntax CTypedLLLExp  ::= "#asBytes32" "(" CTypedLLLExp ")"    [strict]
 // ----------------------------------------------------------------------
    rule #compileExpr(%as_bytes32(EXPR)) => #asBytes32(#compileValueExpr(EXPR))

    rule #asBytes32(@tlll(T, CODE, EXPRATTR))
        => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %num256) orBool #isTypeOf(T, %address),
                       @tlll(%bytes32, CODE, @none),
                       #exception("Function arg type does not match expected type."))


    // slice
    syntax CTypedLLLExp  ::= "#slice" "(" CTypedLLLExp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict]
    syntax CTypedLLLExp  ::= "#sliceAux" "(" TypedLLLExp  ","  // bytes
                                             LLLExp       ","  // start
                                             LLLExp       ","  // length
                                             CTypedLLLExp      // placeholder
                                         ")"      [strict(4)]
 // -----------------------------------------------------------------------------------------------------
    rule #compileExpr(%slice(EXPR, STARTEXPR, LENEXPR))
        => #slice(#compileExpr(EXPR), #compileValueExpr(STARTEXPR), #compileValueExpr(LENEXPR))

    rule #slice(@tlll(%bytesT(L), BYTESCODE, EXPRATTR), @tlll(%num, START, _), @tlll(%num, LEN, _))
        => #sliceAux(@tlll(%bytesT(L), BYTESCODE, EXPRATTR), START, LEN,
                           #newPlaceholder(%bytesT(L +Int 32)))

    rule #sliceAux(@tlll(%bytesT(L), BYTESLOC, @locattr(@storage, MUTABLE)), START, LEN, PLACEHOLDER)
        => #sliceBytesByCopy(@tlll(%bytesT(L),
                                   $add($sha3_32(BYTESLOC), $add($div($_start, 32), 1)),  // first pos is the byte array length
                                   @locattr(@storage, MUTABLE)),
                             L, START, LEN, PLACEHOLDER)

    rule #sliceAux(@tlll(%bytesT(L), BYTESLOC, @locattr(TARGET, MUTABLE)), START, LEN, PLACEHOLDER)
        => #sliceBytesByCopy(@tlll(%bytesT(L),
                                  $add(BYTESLOC, $add($sub($_start, $mod($_start, 32)),32)),  // make sure the byte arrary after copy is still 32-byte aligned.
                                  @locattr(TARGET, MUTABLE)),
                             L, START, LEN, PLACEHOLDER)
      requires TARGET =/=K @storage


    syntax CTypedLLLExp  ::= "#sliceBytesByCopy" "(" TypedLLLExp ","  // source
                                                     Int         ","  // old max length
                                                     LLLExp      ","  // start
                                                     LLLExp      ","  // length
                                                     TypedLLLExp ")"  // placeholder (destination)


    syntax CTypedLLLExp  ::= "#sliceBytesByCopyAux" "(" CLLLExp  ","  // copier
                                                        Int      ","  // placeholder loc
                                                        LLLExp   ","  // start
                                                        LLLExp   ","  // length
                                                        Int      ","  // old max length
                                                        Int           // new max length
                                                     ")"  [strict(1)]
 // -----------------------------------------------------------------
    rule #sliceBytesByCopy(SOURCE, OLDMAXLEN, START, LEN, @tlll(T, PLACEHOLDERLOC, LOCATTR))
        => #sliceBytesByCopyAux(#mkByteSliceCopier(@tlll(T, PLACEHOLDERLOC +Int 32, LOCATTR),
                                                   SOURCE,
                                                   $add($_length, 32),
                                                   OLDMAXLEN),
                                PLACEHOLDERLOC, START, LEN, OLDMAXLEN, LEN)
      requires isInt(LEN)

    rule #sliceBytesByCopy(SOURCE, OLDMAXLEN, START, LEN, @tlll(T, PLACEHOLDERLOC, LOCATTR))
        => #sliceBytesByCopyAux(#mkByteSliceCopier(@tlll(T, PLACEHOLDERLOC +Int 32, LOCATTR),
                                                   SOURCE,
                                                   $add($_length, 32),
                                                   OLDMAXLEN),
                                PLACEHOLDERLOC, START, LEN, OLDMAXLEN, OLDMAXLEN)
      requires notBool isInt(LEN)

    rule #sliceBytesByCopyAux(COPIER, PLACEHOLDERLOC, START, LEN, OLDMAXLEN, NEWMAXLEN)
        => @tlll(%bytesT(NEWMAXLEN), $with($_start, START,
                                      $with($_length, LEN,
                                        $with($_opos, $add(PLACEHOLDERLOC, $mod($_start, 32)),
                                          $%seq(
                                            $assert($lt($add($_start, $_length), OLDMAXLEN)),
                                            COPIER,
                                            $mstore($_opos, $_length),
                                            $_opos,.LLLExps)))), @locattr(@memory, true))


    // as_wei_value
    syntax CTypedLLLExp  ::= "#asWeiValue" "(" Expr "," K ")"    [strict(2)]
 // ------------------------------------------------------------------------
    rule #compileExpr(%as_wei_value(EXPR, UNIT)) => #asWeiValue(EXPR, #convertToWei(UNIT))

    rule #asWeiValue(NUM, DENOMINATION)
        => #asWeiValueNumber(NUM, DENOMINATION)
      requires isInt(NUM) orBool isFixedPoint(NUM)

    rule #asWeiValue(EXPR, DENOMINATION)
        => #asWeiValueLLLExp(#compileValueExpr(EXPR), DENOMINATION)
      requires notBool(isInt(EXPR) orBool isFixedPoint(EXPR))


    syntax CTypedLLLExp  ::= "#asWeiValueNumber" "(" Expr         "," Int ")"
    syntax CTypedLLLExp  ::= "#asWeiValueLLLExp" "(" CTypedLLLExp "," Int ")"  [strict(1)]
 // --------------------------------------------------------------------------------------
    rule #asWeiValueNumber(NUM:Int, DENOMINATION)
        => @tlll(%unitT(%num, %wei |-> 1, false), NUM, @none)

    rule #asWeiValueNumber(%fixed10(NUM, DEN), DENOMINATION)
        => #ifThen((DENOMINATION modInt DEN) =/=Int 0,
                   #exception("Too many decimal places."))
        ~> @tlll(%unitT(%num, %wei |-> 1, false), (NUM *Int DENOMINATION) /Int DEN, @none)

    rule #asWeiValueLLLExp(@tlll(%num, CODE, EXPRATTR), DENOMINATION)
        => @tlll(%unitT(%num, %wei |-> 1, false), $mul(CODE, DENOMINATION), @none)

    rule #asWeiValueLLLExp(@tlll(%decimal, CODE, EXPRATTR), DENOMINATION)
        => @tlll(%unitT(%num, %wei |-> 1, false), $div($mul(CODE, DENOMINATION), @decimalDivisor), @none)


    // num256_add
    syntax CTypedLLLExp  ::= "#num256Add" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileExpr(%num256_add(EXPR1, EXPR2)) => #num256Add(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Add(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($or($iszero(CODE2), $gt($add(CODE1, CODE2), CODE1))),
                            $add(CODE1, CODE2),.LLLExps), @none)


    // num256_sub
    syntax CTypedLLLExp  ::= "#num256Sub" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileExpr(%num256_sub(EXPR1, EXPR2)) => #num256Sub(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Sub(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($ge(CODE1, CODE2)),
                            $sub(CODE1, CODE2),.LLLExps), @none)


    // num256_mul
    syntax CTypedLLLExp  ::= "#num256Mul" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileExpr(%num256_mul(EXPR1, EXPR2)) => #num256Mul(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Mul(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($or($iszero(CODE1), $eq($div($mul(CODE1, CODE2), CODE1), CODE2))),
                            $mul(CODE1, CODE2),.LLLExps), @none)


    // num256_div
    syntax CTypedLLLExp  ::= "#num256Div" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileExpr(%num256_div(EXPR1, EXPR2)) => #num256Div(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Div(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert(CODE2),
                            $div(CODE1, CODE2),.LLLExps), @none)


    // num256_exp
    syntax CTypedLLLExp  ::= "#num256Exp" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileExpr(%num256_exp(EXPR1, EXPR2)) => #num256Exp(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Exp(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($or($or($eq(CODE2, 1), $iszero(CODE2)), $lt(CODE1, $exp(CODE1, CODE2)))),
                            $exp(CODE1, CODE2),.LLLExps), @none)


    // num256_gt
    syntax CTypedLLLExp  ::= "#num256Gt" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // -----------------------------------------------------------------------------------------
    rule #compileExpr(%num256_gt(EXPR1, EXPR2)) => #num256Gt(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Gt(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%bool, $gt(CODE1, CODE2), @none)


    // num256_ge
    syntax CTypedLLLExp  ::= "#num256Ge" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // -----------------------------------------------------------------------------------------
    rule #compileExpr(%num256_ge(EXPR1, EXPR2)) => #num256Ge(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Ge(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%bool, $ge(CODE1, CODE2), @none)


    // num256_lt
    syntax CTypedLLLExp  ::= "#num256Lt" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // -----------------------------------------------------------------------------------------
    rule #compileExpr(%num256_lt(EXPR1, EXPR2)) => #num256Lt(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Lt(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%bool, $lt(CODE1, CODE2), @none)


    // num256_le
    syntax CTypedLLLExp  ::= "#num256Le" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // -----------------------------------------------------------------------------------------
    rule #compileExpr(%num256_le(EXPR1, EXPR2)) => #num256Le(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #num256Le(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%bool, $le(CODE1, CODE2), @none)


    // min
    syntax CTypedLLLExp  ::= "#min" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
    syntax CTypedLLLExp  ::= "#minAux" "(" TypedLLLExp "," TypedLLLExp "," Bool /*num256?*/ ")"
 // -------------------------------------------------------------------------------------------
    rule #compileExpr(%min(EXPR1, EXPR2)) => #min(#compileValueExpr(EXPR1), #compileValueExpr(EXPR2))

    rule #min(@tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(notBool(#isTypeOf(LT, %num) orBool #isTypeOf(LT, %decimal) orBool #isTypeOf(LT, %num256)) orBool
                   notBool(#isTypeOf(RT, %num) orBool #isTypeOf(RT, %decimal) orBool #isTypeOf(RT, %num256)),
                   #exception("Function arg type does not match expected type."))
        ~> #ifThen(notBool(#areUnitsCompatible(LT, RT, #isNumLiteral(LCODE))) andBool
                   notBool(#areUnitsCompatible(RT, LT, #isNumLiteral(RCODE))),
                   #exception("Units must be compatible."))
        ~> #ifThenElse(LT ==K %num256,
                       #minAux(@tlll(#dropUnit(LT), LCODE, LEXPRATTR),
                               @tlll(#dropUnit(RT), RCODE, REXPRATTR), true),
                       #minAux(@tlll(#dropUnit(LT), LCODE, LEXPRATTR),
                               @tlll(#dropUnit(RT), RCODE, REXPRATTR), false))

    // TODO: figure out the result type containing unit or not.



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
    rule #isUnitTypeOf(%unitT(T, _:Map, _), T) => true

    rule #isUnitTypeOf(%unitT(T, _:Map, _), TARGET) => false
      requires T =/=K TARGET


    syntax Bool  ::= "#isTopic" "(" EventParam ")"    [function]
 // ------------------------------------------------------------
    rule #isTopic(%eparam(_, _, ISTOPIC)) => ISTOPIC


    syntax Bool  ::= "#isInMemory" "(" LLLExpAttr ")"    [function]
 // ---------------------------------------------------------------
    rule #isInMemory(@locattr(@memory, _)) => true

    rule #isInMemory(@locattr(@storage, _)) => false

    rule #isInMemory(@locattr(@storage_prehashed, _)) => false

    rule #isInMemory(@none) => false


    syntax Bool  ::= "#isNumLiteral" "(" LLLExp ")"  [function]
 // -----------------------------------------------------------
    rule #isNumLiteral(CODE) => true
      requires isInt(CODE) orBool isFixedPoint(CODE)

    rule #isNumLiteral(CODE) => false
      requires notBool(isInt(CODE) orBool isFixedPoint(CODE))


// Exception
// ======================

    syntax KItem  ::= "#exception" "(" String ")"
 // ---------------------------------------------


// List Concatenation
// ==================


    syntax Defs  ::= Defs "++Def" Defs    [right, function]
 // -------------------------------------------------------
    rule .Defs ++Def DEFS:Defs => DEFS

    rule (DEF DEFS1) ++Def DEFS2 => DEF (DEFS1 ++Def DEFS2)


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
    syntax LLLExps  ::= List{LLLExp, ","}          [klabel(LLLExps)]
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
 // ----------------------------------------------------
    rule .Ids ++Id IDS:Ids   => IDS

    rule (ID IDS1) ++Id IDS2 => ID (IDS1 ++Id IDS2)


    syntax AnnVars  ::= AnnVars "++Annvar" AnnVars  [right, function]
 // -----------------------------------------------------------------
    rule .AnnVars ++Annvar ANNVARS:AnnVars => ANNVARS

    rule (ANNVAR ANNVARS1) ++Annvar ANNVARS2 => ANNVAR (ANNVARS1 ++Annvar ANNVARS2)


    syntax Bytes  ::= Bytes "++Byte" Bytes  [right, function]
 // ---------------------------------------------------------
    rule .Bytes ++Byte BS => BS

    rule (B : BS1) ++Byte BS2 => B : (BS1 ++Byte BS2)


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


    syntax Int  ::= "#numOfExprs"    "(" Exprs ")"          [function]
    syntax Int  ::= "#numOfExprsAux" "(" Exprs "," Int ")"  [function]
 // ------------------------------------------------------------------
    rule #numOfExprs(EXPRS) => #numOfExprsAux(EXPRS, 0)

    rule #numOfExprsAux(.Exprs, NUM) => NUM

    rule #numOfExprsAux((EXPR EXPRS), NUM) => #numOfExprsAux(EXPRS, NUM +Int 1)


    syntax Int  ::= "#numOfParams"    "(" Params ")"          [function]
    syntax Int  ::= "#numOfParamsAux" "(" Params "," Int ")"  [function]
 // --------------------------------------------------------------------
    rule #numOfParams(PARAMS) => #numOfParamsAux(PARAMS, 0)

    rule #numOfParamsAux(.Params, NUM) => NUM

    rule #numOfParamsAux((PARAM PARAMS), NUM) => #numOfParamsAux(PARAMS, NUM +Int 1)


    syntax Int  ::= "#numOfEventParams"    "(" EventParams ")"          [function]
    syntax Int  ::= "#numOfEventParamsAux" "(" EventParams "," Int ")"  [function]
 // ------------------------------------------------------------------------------
    rule #numOfEventParams(EPARAMS) => #numOfEventParamsAux(EPARAMS, 0)

    rule #numOfEventParamsAux(.EventParams, NUM) => NUM

    rule #numOfEventParamsAux((EPARAM EPARAMS), NUM) => #numOfEventParamsAux(EPARAMS, NUM +Int 1)


    syntax Int  ::= "#numOfBytes"    "(" Bytes ")"          [function]
    syntax Int  ::= "#numOfBytesAux" "(" Bytes "," Int ")"  [function]
 // -------------------------------------------------------------------
    rule #numOfBytes(BS) => #numOfBytesAux(BS, 0)

    rule #numOfBytesAux(.Bytes, NUM) => NUM

    rule #numOfBytesAux((B : BS), NUM) => #numOfBytesAux(BS, NUM +Int 1)


    syntax Int  ::= "#numOfTypedLLLExps"    "(" TypedLLLExps ")"          [function]
    syntax Int  ::= "#numOfTypedLLLExpsAux" "(" TypedLLLExps "," Int ")"  [function]
 // --------------------------------------------------------------------------------
    rule #numOfTypedLLLExps(TLLLS) => #numOfTypedLLLExpsAux(TLLLS, 0)

    rule #numOfTypedLLLExpsAux(.TypedLLLExps, NUM) => NUM

    rule #numOfTypedLLLExpsAux((TLLL TLLLS), NUM) => #numOfTypedLLLExpsAux(TLLLS, NUM +Int 1)


    syntax Int  ::= "#numOfAnnVars"    "(" AnnVars ")"          [function]
    syntax Int  ::= "#numOfAnnVarsAux" "(" AnnVars "," Int ")"  [function]
 // ----------------------------------------------------------------------
    rule #numOfAnnVars(ANNVARS) => #numOfAnnVarsAux(ANNVARS, 0)

    rule #numOfAnnVarsAux(.AnnVars, NUM) => NUM

    rule #numOfAnnVarsAux((ANNVAR ANNVARS), NUM) => #numOfAnnVarsAux(ANNVARS, NUM +Int 1)


// Type Related
// ============


    syntax Int  ::= "#sizeOfParams" "(" Params ")"    [function]
    syntax Int  ::= "#sizeOfParam"  "(" Param  ")"    [function]
 // ------------------------------------------------------------
    rule #sizeOfParams(.Params) => 0

    rule #sizeOfParams(P PS)    => #sizeOfParam(P) +Int #sizeOfParams(PS)

    rule #sizeOfParam(%param(_, %bytesT(_))) => 32

    rule #sizeOfParam(%param(_, T)) => #sizeOfType(T)    requires notBool isByteArrayType(T)


    syntax Int  ::= "#sizeOfPackedArgs" "(" TypedLLLExps ")"    [function]
    syntax Int  ::= "#sizeOfPackedArg"  "(" TypedLLLExp  ")"    [function]
 // ----------------------------------------------------------------------
    rule #sizeOfPackedArgs(.TypedLLLExps) => 0

    rule #sizeOfPackedArgs(TLLL TLLLS)    => #sizeOfPackedArg(TLLL) +Int #sizeOfPackedArgs(TLLLS)

    rule #sizeOfPackedArg(@tlll(T, _, _)) => #sizeOfType(T)


    syntax Int  ::= "#sizeOfType" "(" Type ")"     [function]
 // ---------------------------------------------------------
    rule #sizeOfType(T:BaseType) => 32

    rule #sizeOfType(%bytesT(L)) => #ceil32(L) +Int 64

    rule #sizeOfType(%listT(SUBTYPE, N)) => #sizeOfType(SUBTYPE) *Int N

    rule #sizeOfType(%structT(.AnnVars)) => 0

    rule #sizeOfType(%structT(%annvar(_, T) ANNVARS)) => #sizeOfType(T) +Int #sizeOfType(%structT(ANNVARS))


    syntax KItem  ::= "#canonicalizeType" "(" Type "," Bool /*event?*/ ")"
 // ------------------------------------------------------------------------
    rule #canonicalizeType(%bytesT(L), EVENT)
        => #ifThenElse(EVENT ==K true andBool L <=Int 32,
                       "bytes" +String Int2String(L),
                       "bytes")

    rule #canonicalizeType(%listT(SUBTYPE, N), _)
        => #canonicalizeListType(#canonicalizeType(SUBTYPE, false), N)
      requires isBaseType(SUBTYPE) orBool isListType(SUBTYPE)

    rule #canonicalizeType(%listT(SUBTYPE, N), _)
        => #exception("List of byte arrays not allowed.")
      requires isByteArrayType(SUBTYPE)

    rule #canonicalizeType(%num, _) => "int128"

    rule #canonicalizeType(%unitT(%num, _:Unit, _), _) => "int128"

    rule #canonicalizeType(%decimal, _) => "decimal10"

    rule #canonicalizeType(%unitT(%decimal, _:Unit, _), _) => "decimal10"

    rule #canonicalizeType(%num256, _) => "uint256"
   
    rule #canonicalizeType(%bool, _) => "bool"
 
    rule #canonicalizeType(%address, _) => "address"
 
    rule #canonicalizeType(%bytes32, _) => "bytes32"


    syntax KItem  ::= "#canonicalizeListType" "(" K "," Int ")"  [strict(1)]
 // ------------------------------------------------------------------------
    rule #canonicalizeListType(T:String, N)
        => T +String "[" +String Int2String(N) +String "]"


    syntax Int  ::= "#getListTCount" "(" ListType ")"    [function]
 // ---------------------------------------------------------------
    rule #getListTCount(%listT(SUBTYPE, N)) => N


    syntax Int  ::= "#getBytesTLen" "(" ByteArrayType ")"  [function]
 // -----------------------------------------------------------------
    rule #getBytesTLen(%bytesT(L)) => L


    // Convert from one base type to another. Need to call `#unwrapLoc` first.
    syntax CTypedLLLExp  ::= "#baseTypeConvert"    "(" TypedLLLExp "," Type /*to*/ ")"
    syntax CTypedLLLExp  ::= "#baseTypeConvertAux" "(" TypedLLLExp "," Type        ")"
    syntax CTypedLLLExp  ::= "#baseTypeConvertNoUnit" "(" LLLExp ","  // code
                                                          Type   ","  // from
                                                          Type   ")"  // to
 // ----------------------------------------------------------------------------------
    rule #baseTypeConvert(@tlll(FROMT, CODE, EXPRATTR), TOT)
        => #baseTypeConvertAux(#unwrapLoc(@tlll(FROMT, CODE, EXPRATTR)), TOT)

    rule #baseTypeConvertAux(@tlll(FROMT, CODE, _), TOT)
        => #ifThenElse(#areUnitsCompatible(FROMT, TOT, #isNumLiteral(CODE)),
                       #baseTypeConvertNoUnit(CODE, #dropUnit(FROMT), #dropUnit(TOT)),
                       #exception("Typecasting unavailable due to incompatible units"))

    rule #baseTypeConvertNoUnit(CODE, FROMT, TOT)
        => #ifThenElse(notBool(isBaseType(FROMT)) orBool notBool(isBaseType(TOT)),
                       #exception("Base type conversion from or to non-base type."),
             #ifThenElse(FROMT ==K TOT,
                         @tlll(TOT, CODE, @none),
               #ifThenElse(FROMT ==K %num andBool TOT ==K %decimal,
                           @tlll(TOT, $mul(CODE, @decimalDivisor), @none),
                 #ifThenElse(FROMT ==K %num256 andBool TOT ==K %num,
                             @tlll(TOT, $uclample(CODE, $mload(@maxNumPos)), @none),
                             #exception("Typecasting unavailable.")))))


    syntax CParams  ::= "#parseTypeForParams" "(" Params "," Params ")"
    syntax KItem    ::= "#parseTypeForParam"  "(" Id "," CType  ")"  [strict(2)]
 // ----------------------------------------------------------------------------
    rule #parseTypeForParams(.Params, RESULT) => RESULT

    rule #parseTypeForParams(%param(NAME, T) PARAMS, RESULT)
        => #parseTypeForParam(NAME, #parseType(T, true))
        ~> #parseTypeForParams(PARAMS, RESULT)

    rule #parseTypeForParam(NAME, T:Type) => %param(NAME, T)

    rule PARAM:Param ~> #parseTypeForParams(PARAMS, RESULT)
        => #parseTypeForParams(PARAMS, RESULT ++Param (PARAM .Params))


    syntax CEventParams  ::= "#parseTypeForEventParams" "(" EventParams "," EventParams")"
    syntax KItem         ::= "#parseTypeForEventParam"  "(" Id "," CType "," Bool ")"  [strict(2)]
 // ----------------------------------------------------------------------------------------------
    rule #parseTypeForEventParams(.EventParams, RESULT) => RESULT

    rule #parseTypeForEventParams(%eparam(NAME, T, TOPIC) EPARAMS, RESULT)
        => #parseTypeForEventParam(NAME, #parseType(T, true), TOPIC)
        ~> #parseTypeForEventParams(EPARAMS, RESULT)

    rule #parseTypeForEventParam(NAME, T:Type, TOPIC) => %eparam(NAME, T, TOPIC)

    rule EPARAM:EventParam ~> #parseTypeForEventParams(EPARAMS, RESULT)
        => #parseTypeForEventParams(EPARAMS, RESULT ++Eparam (EPARAM .EventParams))


    syntax CType  ::= "#parseType" "(" Type "," Bool /*in memory?*/ ")"
 // -------------------------------------------------------------------
    rule #parseType(%void, _) => %void

    rule #parseType(%bool, _) => %bool

    rule #parseType(%num, _) => %num

    rule #parseType(%decimal, _) => %decimal

    rule #parseType(%unitT(T, UNIT:Map, POSITIONAL), _) => %unitT(T, UNIT, POSITIONAL)

    rule #parseType(%unitT(T, UNIT:Unit, POSITIONAL), _)
        => #parseUnitType(%unitT(T, UNIT, POSITIONAL))

    rule #parseType(%num256, _) => %num256

    rule #parseType(%signed256, _) => %signed256

    rule #parseType(%bytes32, _) => %bytes32

    rule #parseType(%address, _) => %address

    rule #parseType(%bytesT(L), _) => %bytesT(L)

    rule #parseType(%listT(SUBTYPE, N), INMEM) => #parseListType(#parseType(SUBTYPE, INMEM), N)

    rule #parseType(%mapT(KT, VT), true)
        => #exception("No mappings allowed for in-memory types, only fixed-size arrays")

    rule #parseType(%mapT(KT, VT), false)
        => #ifThenElse(isBaseType(KT) orBool isByteArrayType(KT),
                       #parseMapType(#parseType(KT, false), #parseType(VT, false)),
                       #exception("Mapping keys must be base or bytes types"))

    rule #parseType(%structT(ANNVARS), INMEM) => #parseStructType(ANNVARS, INMEM, .Ids, .AnnVars)

    // TODO: support Tuple

    // Special Types
    rule #parseType(%timestamp, _)       => %unitT(%num, %sec |-> 1, true)

    rule #parseType(%timedelta, _)       => %unitT(%num, %sec |-> 1, false)

    rule #parseType(%currency_value, _)  => %unitT(%num, %currency |-> 1, false)

    rule #parseType(%currency1_value, _) => %unitT(%num, %currency1 |-> 1, false)

    rule #parseType(%currency2_value, _) => %unitT(%num, %currency2 |-> 1, false)

    rule #parseType(%wei_value, _)       => %unitT(%num, %wei |-> 1, false)


    syntax CType  ::= "#parseListType" "(" CType "," Int ")"    [strict(1)]
 // --------------------------------------------------------------------
    rule #parseListType(T, N) => %listT(T, N)


    syntax CType  ::= "#parseMapType" "(" CType "," CType ")"    [seqstrict]
 // ------------------------------------------------------------------------
    rule #parseMapType(KT, VT) => %mapT(KT, VT)


    syntax CType  ::= "#parseStructType" "(" AnnVars "," Bool "," Ids "," AnnVars ")"
    syntax KItem  ::= "#nameWithType" "(" Id "," CType ")"    [strict(2)]
 // ---------------------------------------------------------------------------------
    rule #parseStructType(.AnnVars, _, _, ANNVARS) => %structT(ANNVARS)

    rule #parseStructType(%annvar(NAME, T) ANNVARS, INMEM, NAMES, RESULT)
        => #ifThen(notBool #isVarNameValid(NAME),
                   #exception("Invalid member variable for struct."))
        ~> #ifThen(#inIds(NAME, NAMES),
                   #exception("Member variable duplicated: " +String Id2String(NAME)))
        ~> #nameWithType(NAME, #parseType(T, INMEM))
        ~> #parseStructType(ANNVARS, INMEM, NAMES, RESULT)

    rule #nameWithType(NAME, T:Type) ~> #parseStructType(ANNVARS, INMEM, NAMES, RESULT)
        => #parseStructType(ANNVARS, INMEM, NAMES ++Id (NAME .Ids), RESULT ++Annvar (%annvar(NAME, T) .AnnVars))

// Units
// =====


    syntax UnitType  ::= "%unitT" "(" PureNumType "," Map "," Bool /*positional*/ ")"
    syntax CType     ::= "#parseUnitType" "(" UnitType ")"    [function]
 // ---------------------------------------------------------------------------------
     rule #parseUnitType(%unitT(T, UNIT:Unit, POSITIONAL))
         => %unitT(T, #parseUnit(UNIT), POSITIONAL)


    syntax Map  ::= "#parseUnit" "(" Unit ")"    [function]
 // -------------------------------------------------------
     rule #parseUnit(U1) => (U1 |-> 1)
       requires isBaseUnit(U1)

     rule #parseUnit(%umul(U1, U2))
         => #combineUnits(#parseUnit(U1), #parseUnit(U2), false)

     rule #parseUnit(%udiv(U1, U2))
         => #combineUnits(#parseUnit(U1), #parseUnit(U2), true)

     rule #parseUnit(%upow(U1, EXP))
         => (U1 |-> EXP)


    syntax Map  ::= "#combineUnits"    "(" Map "," Map "," Bool /*div?*/")"  [function]
    syntax Map  ::= "#combineUnitsAux" "(" Map "," Map "," Bool ","
                                           Set ","  // union of the keys of two maps
                                           Map      // merged result
                                        ")"                                  [function]
 // -----------------------------------------------------------------------------------
    rule #combineUnits(M1, M2, DIV)
        => #combineUnitsAux(M1, M2, DIV, keys(M1) keys(M2), .Map)

    rule #combineUnitsAux(_, _, _, .Set, UNITMAP) => #removeZeros(UNITMAP)

    rule #combineUnitsAux(M1, M2, true, SetItem(KEY:BaseUnit) KEYS, UNITMAP)
        => #combineUnitsAux(M1, M2, true, KEYS,
                            UNITMAP[KEY <- #lookupUnitMap(M1, KEY, 0) -Int #lookupUnitMap(M2, KEY, 0)])

    rule #combineUnitsAux(M1, M2, false, SetItem(KEY:BaseUnit) KEYS, UNITMAP)
        => #combineUnitsAux(M1, M2, false, KEYS,
                            UNITMAP[KEY <- #lookupUnitMap(M1, KEY, 0) +Int #lookupUnitMap(M2, KEY, 0)])


    syntax Map  ::= "#removeZeros" "(" Map ")"  [function]
 // ------------------------------------------------------
    rule #removeZeros(.Map) => .Map

    rule #removeZeros( KEY |-> 0     REST ) => #removeZeros(REST)

    rule #removeZeros( KEY |-> VALUE REST ) => KEY |-> VALUE #removeZeros(REST)
      requires VALUE =/=K 0


    syntax Int  ::= "#lookupUnitMap" "(" Map      ","
                                         BaseUnit ","
                                         Int           // default value
                                     ")"   [function]
 // -------------------------------------------------------------------
    rule #lookupUnitMap((KEY |-> VALUE) REST, KEY, DEFAULT) => VALUE

    rule #lookupUnitMap(M, KEY, DEFAULT) => DEFAULT
      requires notBool KEY in_keys(M)


    syntax Map  ::= "#computeUnitPow" "(" Map "," Int ")"  [function]
 // -----------------------------------------------------------------
    rule #computeUnitPow(.Map, POW) => .Map

    rule #computeUnitPow((KEY |-> VALUE:Int) REST, POW)
        => (KEY |-> VALUE *Int POW) #computeUnitPow(REST, POW)


    syntax Type  ::= "#dropUnit" "(" Type ")"    [function]
 // -------------------------------------------------------
    rule #dropUnit(T) => T
      requires notBool isUnitType(T)

    rule #dropUnit(%unitT(%num, _:Map, _)) => %num

    rule #dropUnit(%unitT(%decimal, _:Map, _)) => %decimal


    syntax UnitType  ::= "#convertToUnitIfPure" "(" NumericType "," UnitTuple ")"    [function]
 // -------------------------------------------------------------------------------------------
    rule #convertToUnitIfPure(T, _) => T
      requires isUnitType(T)

    rule #convertToUnitIfPure(%num, @unittuple(UNITMAP, POSITIONAL))
        => %unitT(%num, UNITMAP, POSITIONAL)

    rule #convertToUnitIfPure(%decimal, @unittuple(UNITMAP, POSITIONAL))
        => %unitT(%decimal, UNITMAP, POSITIONAL)


    syntax Bool  ::= "#areUnitsCompatible" "(" Type ","  // from type
                                               Type ","  // to type
                                               Bool      // is from a number literal?
                                           ")"  [function]
 // ------------------------------------------------------
    rule #areUnitsCompatible(FROM, TO, _) => true
      requires notBool(isUnitType(FROM)) andBool notBool(isUnitType(TO))

    rule #areUnitsCompatible(FROM, TO, true) => true
      requires notBool(isUnitType(FROM)) andBool isUnitType(TO)

    rule #areUnitsCompatible(FROM, TO, false) => false
      requires notBool(isUnitType(FROM)) andBool isUnitType(TO)

    rule #areUnitsCompatible(FROM, TO, _) => false
      requires isUnitType(FROM) andBool notBool(isUnitType(TO))

    rule #areUnitsCompatible(%unitT(_, FROMMAP:Map, FROMPOSITIONAL), %unitT(_, TOMAP:Map, TOPOSITIONAL), _)
        => true
      requires FROMMAP ==K TOMAP andBool FROMPOSITIONAL ==K TOPOSITIONAL

    rule #areUnitsCompatible(%unitT(_, FROMMAP:Map, FROMPOSITIONAL), %unitT(_, TOMAP:Map, TOPOSITIONAL), _)
        => false
      requires FROMMAP =/=K TOMAP orBool FROMPOSITIONAL =/=K TOPOSITIONAL


// Bytes
// =====


    syntax Bytes  ::= ".Bytes" | Int ":" Bytes


    syntax CBytes  ::= "#string2Bytes"         "(" String ")"
    syntax CBytes  ::= "#string2BytesAux"      "(" String "," Bytes ")"
    syntax CBytes  ::= "#nonEmptyString2Bytes" "(" String "," Bytes ")"
 // --------------------------------------------------------------------
    rule #string2Bytes(STR) => #string2BytesAux(STR, .Bytes)

    rule #string2BytesAux(STR, RESULT) => RESULT
      requires lengthString(STR) ==Int 0

    rule #string2BytesAux(STR, RESULT)
        => #nonEmptystring2Bytes(STR, RESULT)
      requires lengthString(STR) >Int 0

    rule #nonEmptystring2Bytes(STR, RESULT)
        => #string2BytesAux(substrString(STR, 1, lengthString(STR)),
                            RESULT ++Byte (ordChar(substrString(STR, 0, 1)) : .Bytes))
      requires ordChar(substrString(STR, 0, 1)) <Int 256

    rule #nonEmptystring2Bytes(STR, RESULT)
        => #exception("Cannot insert special character into byte array")
      requires ordChar(substrString(STR, 0, 1)) >=Int 256


    //if length(bytes) < width, pad zeros to the right
    syntax Int  ::= "#bytes2Int" "(" Bytes "," Int /*width*/ "," Int /*result*/ ")"  [function]
 // -------------------------------------------------------------------------------------------
    rule #bytes2Int(BS, 0, RESULT) => RESULT

    rule #bytes2Int(.Bytes, WIDTH, RESULT) => #bytes2Int(.Bytes, WIDTH -Int 1, RESULT *Int 256)
      requires WIDTH >Int 0

    rule #bytes2Int(B : BS, WIDTH, RESULT) => #bytes2Int(BS, WIDTH -Int 1, RESULT *Int 256 +Int B)
      requires WIDTH >Int 0


    syntax Bytes  ::= "#take" "(" Int "," Bytes ")"   [function]
 // ------------------------------------------------------------
    rule #take(0, BS)       => .Bytes

    rule #take(N, .Bytes)   => 0 : #take(N -Int 1, .Bytes)    requires N >Int 0

    rule #take(N, (B : BS)) => B : #take(N -Int 1, BS)        requires N >Int 0


    syntax Bytes  ::= "#drop" "(" Int "," Bytes ")"  [function]
 // -----------------------------------------------------------
    rule #drop(0, BS)       => BS

    rule #drop(N, .Bytes)   => .Bytes

    rule #drop(N, (B : BS)) => #drop(N -Int 1, BS)    requires N >Int 0


    syntax TypedLLLExp  ::= "#byteArray2Num"  "(" TypedLLLExp "," Type "," Int ")"
 // ------------------------------------------------------------------------------


// Compute signatures
// ==================


    syntax KItem  ::= "#computeEventId"    "(" Id "," EventParams ")"
    syntax KItem  ::= "#computeEventIdAux"
 // -----------------------------------------------------------------
    rule #computeEventId(NAME, EPARAMS)
        => #computeEventSig(Id2String(NAME) +String "(", EPARAMS)
        ~> #computeEventIdAux

    rule EVENTSIG:String ~> #computeEventIdAux
        => String2Base(Keccak256(EVENTSIG), 16)


    syntax KItem  ::= "#computeEventSig"    "(" String "," EventParams ")"
    syntax KItem  ::= "#computeEventSigAux" "(" String "," EventParams ")"
 // ----------------------------------------------------------------------
    rule #computeEventSig(SIG, %eparam(_, T, _) EPARAMS)
        => #canonicalizeType(T, true)
        ~> #computeEventSigAux(SIG, EPARAMS)

    rule TYPE:String ~> #computeEventSigAux(SIG, EPARAM1 EPARAMS)
        => #computeEventSig(SIG +String TYPE +String ",", EPARAM1 EPARAMS)

    rule TYPE:String ~> #computeEventSigAux(SIG, .EventParams)
        => #computeEventSig(SIG +String TYPE, .EventParams)

    rule #computeEventSig(SIG, .EventParams) => SIG +String ")"


    syntax KItem  ::= "#computeFuncId"  "(" Id "," Params ")"
    syntax KItem  ::= "#computeFuncIdAux"
 // ---------------------------------------------------------
    rule #computeFuncId(FNAME, PARAMS)
        => #computeFuncSig(Id2String(FNAME) +String "(", PARAMS)
        ~> #computeFuncIdAux

    rule FUNCSIG:String ~> #computeFuncIdAux
        => String2Base(substrString(Keccak256(FUNCSIG), 0, 8), 16)

    syntax KItem  ::= "#computeFuncSig"    "(" String "," Params ")"
    syntax KItem  ::= "#computeFuncSigAux" "(" String "," Params ")"
 // ----------------------------------------------------------------
    rule #computeFuncSig(SIG, %param(_,T) PARAMS)
        => #canonicalizeType(T, false)
        ~> #computeFuncSigAux(SIG, PARAMS)

    rule TYPE:String ~> #computeFuncSigAux(SIG, PARAM1 PARAMS)
        => #computeFuncSig(SIG +String TYPE +String ",", PARAM1 PARAMS)

    rule TYPE:String ~> #computeFuncSigAux(SIG, .Params)
        => #computeFuncSig(SIG +String TYPE, .Params)

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
      requires notBool %var(NAME) in_keys(ENV)

    rule <k> #lookupVar(%svar(NAME)) => @tlll(T, LOC, LOCATTR) ... </k>
         <global> %svar(NAME) |-> @taddr(T, LOC, LOCATTR) GLOBAL </global>

    rule <k> #lookupVar(%svar(NAME))
            => #exception("Persistent variable undeclared: " +String Id2String(NAME)) ... </k>
         <global> GLOBAL </global>
      requires notBool %svar(NAME) in_keys(GLOBAL)

    rule #lookupVar(%subscript(V, EXPR))
        => #lookupSubscriptVar(#lookupVar(V), #compileValueExpr(EXPR))

    rule #lookupVar(%attribute(V, NAME))
        => #lookupAttributeVar(#lookupVar(V), NAME)


    syntax CTypedLLLExp  ::= "#lookupSubscriptVar" "(" CTypedLLLExp ","
                                                       CTypedLLLExp
                                                   ")"      [seqstrict]
 // -------------------------------------------------------------------
    rule #lookupSubscriptVar(SUBEXPR, INDEXEXPR)
        => #addVarOffset(SUBEXPR, INDEXEXPR)


    syntax CTypedLLLExp  ::= "#lookupAttributeVar" "(" CTypedLLLExp ","
                                                       Id
                                                   ")"      [strict(1)]
 // -------------------------------------------------------------------
    rule #lookupAttributeVar(SUBEXPR, FILEDNAME)
        => #addVarOffset(SUBEXPR, @tlll(%void, FILEDNAME, @none))


    syntax CTypedLLLExp  ::= "#addVarOffset" "(" TypedLLLExp ","  // base
                                                 TypedLLLExp ")"  // index
 // ------------------------------------------------------------
    // List
    rule #addVarOffset(@tlll(%listT(SUBTYPE, N), BASELOC, LOCATTR), TINDEX)
        => #addListVarOffset(@tlll(%listT(SUBTYPE, N), BASELOC, LOCATTR),
                             #baseTypeConvert(TINDEX, %num))

    // Map, index is not byte array
    rule #addVarOffset(@tlll(%mapT(KT, VT), BASELOC, LOCATTR),
                       @tlll(INDEXT, INDEX, EXPRATTR))
        => #addMapVarOffset(@tlll(%mapT(KT, VT), BASELOC, LOCATTR),
                            #baseTypeConvert(@tlll(INDEXT, INDEX, EXPRATTR), KT))
      requires notBool(isByteArrayType(INDEXT))

    // Map, index is byte array
    rule #addVarOffset(@tlll(%mapT(KT, VT), BASELOC, LOCATTR),
                       @tlll(INDEXT, INDEX, EXPRATTR))
        => #addMapVarOffset(@tlll(%mapT(KT, VT), BASELOC, LOCATTR),
                            #mapKeyByteArrayConvert(@tlll(INDEXT, INDEX, EXPRATTR), KT))
      requires isByteArrayType(INDEXT)

    // Struct
    rule #addVarOffset(@tlll(%structT(ANNVARS), BASELOC, LOCATTR), @tlll(_, INDEXNAME, _))
        => #addStructVarOffset(@tlll(%structT(ANNVARS), BASELOC, LOCATTR),
                               ANNVARS, 0, INDEXNAME)


    syntax CTypedLLLExp  ::= "#mapKeyByteArrayConvert" "(" TypedLLLExp "," Type ")"
 // -------------------------------------------------------------------------------
    // TODO: finish map key conversion


    syntax CTypedLLLExp  ::= "#addListVarOffset" "(" TypedLLLExp  ","
                                                     CTypedLLLExp ")"  [strict(2)]
 // ------------------------------------------------------------------------------
    rule #addListVarOffset(@tlll(%listT(SUBTYPE, N), BASELOC, @locattr(@storage, MUTABLE)),
                           @tlll(_, INDEX, _))
        => @tlll(SUBTYPE, $add($sha3_32(BASELOC), $uclamplt(INDEX, N)), @locattr(@storage, MUTABLE))

    rule #addListVarOffset(@tlll(%listT(SUBTYPE, N), BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                          @tlll(_, INDEX, _))
        => @tlll(SUBTYPE, $add(BASELOC, $uclamplt(INDEX, N)), @locattr(@storage, MUTABLE))

    rule #addListVarOffset(@tlll(%listT(SUBTYPE, N), BASELOC, @locattr(@memory, MUTABLE)),
                           @tlll(_, INDEX, _))
        => @tlll(SUBTYPE, $add($mul(#sizeOfType(SUBTYPE), $uclamplt(INDEX, N)), BASELOC), @locattr(@memory, MUTABLE))


    syntax CTypedLLLExp  ::= "#addMapVarOffset" "(" TypedLLLExp  ","
                                                    CTypedLLLExp ")"  [strict(2)]
 // -----------------------------------------------------------------------------
    rule #addMapVarOffset(@tlll(%mapT(KT, VT), BASELOC, @locattr(@storage, MUTABLE)),
                          @tlll(_, INDEX, _))
        => @tlll(VT, $add($sha3_32(BASELOC), INDEX), @locattr(@storage, MUTABLE))

    rule #addMapVarOffset(@tlll(%mapT(KT, VT), BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                          @tlll(_, INDEX, _))
        => @tlll(VT, $add(BASELOC, INDEX), @locattr(@storage, MUTABLE))

    rule #addMapVarOffset(@tlll(%mapT(KT, VT), _, @locattr(@memory, _)), _)
        => #exception("Can only have fixed-side arrays in memory, not mappings")


    syntax CTypedLLLExp  ::= "#addStructVarOffset" "(" TypedLLLExp ","  // parent
                                                       AnnVars     ","  // struct fields
                                                       Int         ","  // offset
                                                       LLLExp      ")"  // index name
 // ------------------------------------------------------------------
    // storage
    rule #addStructVarOffset(@tlll(_, BASELOC, @locattr(@storage, MUTABLE)),
                             %annvar(FIELDNAME, FIELDT) ANNVARS, OFFSET,
                             INDEXNAME)
        => @tlll(FIELDT, $add($sha3_32(BASELOC), OFFSET), @locattr(@storage, MUTABLE))
      requires INDEXNAME ==K FIELDNAME

    rule #addStructVarOffset(@tlll(BASET, BASELOC, @locattr(@storage, MUTABLE)),
                             %annvar(FIELDNAME, FIELDT) ANNVARS, OFFSET,
                             INDEXNAME)
        => #addStructVarOffset(@tlll(BASET, BASELOC, @locattr(@storage, MUTABLE)),
                               ANNVARS, OFFSET +Int 1, INDEXNAME)
      requires INDEXNAME =/=K FIELDNAME

    // storage prehashed
    rule #addStructVarOffset(@tlll(_, BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                             %annvar(FIELDNAME, FIELDT) ANNVARS, OFFSET,
                             INDEXNAME)
        => @tlll(FIELDT, $add(BASELOC, OFFSET), @locattr(@storage, MUTABLE))
      requires INDEXNAME ==K FIELDNAME

    rule #addStructVarOffset(@tlll(BASET, BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                             %annvar(FIELDNAME, FIELDT) ANNVARS, OFFSET,
                             INDEXNAME)
        => #addStructVarOffset(@tlll(BASET, BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                               ANNVARS, OFFSET +Int 1, INDEXNAME)
      requires INDEXNAME =/=K FIELDNAME

    // memory
    rule #addStructVarOffset(@tlll(_, BASELOC, @locattr(@memory, MUTABLE)),
                             %annvar(FIELDNAME, FIELDT) ANNVARS, OFFSET,
                             INDEXNAME)
        => @tlll(FIELDT, $add(OFFSET, BASELOC), @locattr(@memory, MUTABLE))
      requires INDEXNAME ==K FIELDNAME

    rule #addStructVarOffset(@tlll(BASET, BASELOC, @locattr(@memory, MUTABLE)),
                             %annvar(FIELDNAME, FIELDT) ANNVARS, OFFSET,
                             INDEXNAME)
        => #addStructVarOffset(@tlll(BASET, BASELOC, @locattr(@memory, MUTABLE)),
                               ANNVARS, OFFSET +Int #sizeOfType(FIELDT), INDEXNAME)
      requires INDEXNAME =/=K FIELDNAME


    syntax CTypedLLLExp  ::= "#newVar" "(" Id "," Type ")"
 // ------------------------------------------------------
    rule <k> #newVar(NAME, T) => @tlll(T, LOC, @locattr(@memory, true)) ...</k>
         <env> ENV => ENV[%var(NAME) <- @taddr(T, LOC, @locattr(@memory, true))] </env>
         <nextMem> LOC => LOC +Int #sizeOfType(T) </nextMem>
      requires notBool %var(NAME) in_keys(ENV)

    rule <k> #new(NAME, T)
           => #exception("Duplicate variable name: " +String Id2String(NAME)) ...</k>
         <env> ENV </env>
      requires %var(NAME) in_keys(ENV)


    syntax CTypedLLLExp  ::= "#lookupOrNewVar" "(" Var "," Type ")"
 // ---------------------------------------------------------------
    rule <k> #lookupOrNewVar(%var(NAME), _) => @tlll(T, LOC, LOCATTR) ... </k>
         <env> %var(NAME) |-> @taddr(T, LOC, LOCATTR) ENV </env>

    rule <k> #lookupOrNewVar(%var(NAME), T) => #newVar(NAME, T) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in_keys(ENV)

    rule #lookupOrNewVar(%svar(NAME), _) => #lookupVar(%svar(NAME))

    rule #lookupOrNewVar(%subscript(V, EXPR), _) => #lookupVar(%subscript(V, EXPR))

    rule #lookupOrNewVar(%attribute(V, FILEDNAME), _) => #lookupVar(%attribute(V, FILEDNAME))


    syntax CTypedLLLExp  ::= "#newLoopVar" "(" Id "," Type ")"
 // ----------------------------------------------------------
    rule <k> #newLoopVar(NAME, T) => #exception("Duplicate iter: " +String Id2String(NAME)) ... </k>
         <forvar> FORVARS </forvar>
      requires %var(NAME) in FORVARS

    rule <k> #newLoopVar(NAME, T) => #newVar(NAME, T) ... </k>
         <forvar> FORVARS (.Set => SetItem(%var(NAME))) </forvar>
      requires notBool %var(NAME) in FORVARS


    syntax CTypedLLLExp  ::= "#newPlaceholder" "(" Type ")"
 // -------------------------------------------------------
    rule <k> #newPlaceholder(T)
           => #newVar(String2Id("_placeholder_" +String Int2String(I)), T) ... </k>
         <placeholder> I => I +Int 1 </placeholder>


// Others
// ======


    syntax TypedLLLExp ::= "#unwrapLoc" "(" TypedLLLExp ")"  [function]
 // -------------------------------------------------------------------
    rule #unwrapLoc(@tlll(T, CODE, @locattr(@memory, _)))  => @tlll(T, $mload(CODE), @none)

    rule #unwrapLoc(@tlll(T, CODE, @locattr(@storage, _))) => @tlll(T, $sload(CODE), @none)

    rule #unwrapLoc(@tlll(T, CODE, @none))                 => @tlll(T, CODE, @none)


    syntax KItem  ::= "#convertToWei" "(" Id ")"
 // --------------------------------------------
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


    syntax Bool  ::= "#isVarNameValid" "(" Id ")"  [function]
 // ---------------------------------------------------------
    rule #isVarNameValid(NAME) => true
      requires notBool isReservedWord(NAME)

    rule #isVarNameValid(NAME) => false
      requires isReservedWord(NAME)


    syntax CLLLExps  ::= "#mkByteArrayCopier" "(" TypedLLLExp "," TypedLLLExp ")"
    syntax CLLLExps  ::= "#mkByteArrayCopierAux" "(" TypedLLLExp "," TypedLLLExp ")"
 // --------------------------------------------------------------------------------
    rule #mkByteArrayCopier(@tlll(DESTT, DESTCODE, DATTR),
                            @tlll(SOURCET, SOURCECODE, SATTR))
        => #ifThenElse(#getBytesTLen(SOURCET) >Int #getBytesTLen(DESTT),
                       #exception("Cannot cast from greater max-length to shorter max-length."),
                       #mkByteArrayCopierAux(@tlll(DESTT, DESTCODE, DATTR),
                                             @tlll(SOURCET, SOURCECODE, SATTR)))

    // memory to memory
    rule #mkByteArrayCopierAux(@tlll(DESTT, DESTCODE, @locattr(@memory, _)),
                               @tlll(SOURCET, SOURCECODE, @locattr(@memory, _)))
        => $with($_source, SOURCECODE,
             $with($_sz, $add(32, $mload($_source)),
               $assert($call($add(18, $div($_sz, 10)), 4, 0, $_source, $_sz, DESTCODE, $_sz)))),.LLLExps

    // storage to memory
    rule #mkByteArrayCopierAux(@tlll(DESTT, DESTCODE, @locattr(@memory, DESTMUTABLE)),
                               @tlll(%bytesT(SLEN), SOURCECODE, @locattr(@storage, SOURCEMUTABLE)))
        => #copyByteArrayBySlice(SOURCECODE,
                                 #mkByteSliceCopier(@tlll(DESTT, DESTCODE, @locattr(@memory, DESTMUTABLE)),
                                                    @tlll(%bytesT(SLEN), $sha3_32($_pos), @locattr(@storage, SOURCEMUTABLE)),
                                                    $add($sload($_pos), 32),
                                                    SLEN +Int 32))

    // memory to storage
    rule #mkByteArrayCopierAux(@tlll(DESTT, DESTCODE, @locattr(@storage, DESTMUTABLE)),
                               @tlll(%bytesT(SLEN), SOURCECODE, @locattr(@memory, SOURCEMUTABLE)))
        => #copyByteArrayBySlice(SOURCECODE,
                                 #mkByteSliceCopier(@tlll(DESTT, $sha3_32(DESTCODE), @locattr(@storage, DESTMUTABLE)),
                                                    @tlll(%bytesT(SLEN), $_pos, @locattr(@memory, SOURCEMUTABLE)),
                                                    $add($mload($_pos), 32),
                                                    SLEN +Int 32))

    // storage to storage
    rule #mkByteArrayCopierAux(@tlll(DESTT, DESTCODE, @locattr(@storage, DESTMUTABLE)),
                               @tlll(%bytesT(SLEN), SOURCECODE, @locattr(@storage, SOURCEMUTABLE)))
        => #copyByteArrayBySlice(SOURCECODE,
                                 #mkByteSliceCopier(@tlll(DESTT, $sha3_32(DESTCODE), @locattr(@storage, DESTMUTABLE)),
                                                    @tlll(%bytesT(SLEN), $sha3_32($_pos), @locattr(@storage, SOURCEMUTABLE)),
                                                    $add($sload($_pos), 32),
                                                    SLEN +Int 32))


    syntax CLLLExps  ::= "#copyByteArrayBySlice" "(" LLLExp ","  // source Loc
                                                     CLLLExp     // copy code
                                                 ")"     [strict(2)]
 // ---------------------------------------------------------------------------
    rule #copyByteArrayBySlice(SOURCECODE, SLICECOPIERCODE)
        => $with($_pos, SOURCECODE, SLICECOPIERCODE),.LLLExps


    syntax CLLLExp  ::= "#mkByteSliceCopier" "(" TypedLLLExp ","  // destination
                                                 TypedLLLExp ","  // source
                                                 LLLExp      ","  // length
                                                 Int         ")"  // max length

    syntax CLLLExp  ::= "#mkByteSliceCopierAux" "(" LLLExp      ","  // destination code
                                                    LLLExp      ","  // source code
                                                    LLLExp      ","  // length
                                                    Int         ","  // max length
                                                    LLLExp      ","  // setter
                                                    LLLExp      ")"  // checker
 // ---------------------------------------------------------------
    // memory to memory
    rule #mkByteSliceCopier(@tlll(DESTT, DESTCODE, @locattr(@memory, _)),
                            @tlll(SOURCET, SOURCECODE, @locattr(@memory, _)),
                            LEN,
                            MAXLEN)
        => $with($_l, MAXLEN,
             $pop($call(18 +Int (MAXLEN /Int 10), 4, 0, SOURCECODE, $_l, DESTCODE, $_l)))

    // storage to memory
    rule #mkByteSliceCopier(@tlll(DESTT, DESTCODE, @locattr(@memory, _)),
                            @tlll(SOURCET, SOURCECODE, @locattr(@storage, _)),
                            LEN,
                            MAXLEN)
        => #mkByteSliceCopierAux(DESTCODE, SOURCECODE, LEN, MAXLEN,
                                 $mstore($add($_opos, $mul(32, $mload(@freeLoopIndexPos))),
                                         $sload($add($_pos, $mload(@freeLoopIndexPos)))),
                                 #byteSliceCopyChecker)

    // memory to storage
    rule #mkByteSliceCopier(@tlll(DESTT, DESTCODE, @locattr(@storage, _)),
                            @tlll(SOURCET, SOURCECODE, @locattr(@memory, _)),
                            LEN,
                            MAXLEN)
        => #mkByteSliceCopierAux(DESTCODE, SOURCECODE, LEN, MAXLEN,
                                 $sstore($add($_opos, $mload(@freeLoopIndexPos)),
                                         $mload($add($_pos, $mul(32, $mload(@freeLoopIndexPos))))),
                                 #byteSliceCopyChecker)

    // storage to storage
    rule #mkByteSliceCopier(@tlll(DESTT, DESTCODE, @locattr(@storage, _)),
                            @tlll(SOURCET, SOURCECODE, @locattr(@storage, _)),
                            LEN,
                            MAXLEN)
        => #mkByteSliceCopierAux(DESTCODE, SOURCECODE, LEN, MAXLEN,
                                 $sstore($add($_opos, $mload(@freeLoopIndexPos)),
                                         $sload($add($_pos, $mload(@freeLoopIndexPos)))),
                                 #byteSliceCopyChecker)

    rule #mkByteSliceCopierAux(DESTCODE, SOURCECODE, LEN, MAXLEN, SETTER, CHECKER)
        => $with($_pos, SOURCECODE,
             $with($_opos, DESTCODE,
               $with($_actual_len, LEN,
                 $repeat(@freeLoopIndexPos, 0, (MAXLEN +Int 31) /Int 32,
                         $%seq((CHECKER,.LLLExps) ++LLL (SETTER,.LLLExps))))))


    syntax LLLExp  ::= "#byteSliceCopyChecker"    [function]
 // --------------------------------------------------------
    rule #byteSliceCopyChecker => $if($gt($mul(32, $mload(@freeLoopIndexPos)), $_actual_len),
                                      $break)


    syntax CTypedLLLExp  ::= "#getLength" "(" TypedLLLExp ")"
 // --------------------------------------------------------
    rule #getLength(@tlll(_, LOC, @locattr(@memory, _))) => @tlll(%num, $mload(LOC), @none)

    rule #getLength(@tlll(_, LOC, @locattr(@storage, _))) => @tlll(%num, $mload($sha3_32(LOC)), @none)

endmodule
