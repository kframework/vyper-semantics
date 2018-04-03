/* Vyper source code:
 * https://github.com/ethereum/vyper/commit/8c6000b16e11127462506fd0ac632ce535491bec
 */

require "../common/vyper-abstract-syntax.k"
require "../common/lll-abstract-syntax.k"
require "vyper-lll-utils.k"
require "domains.k"

module VYPER-LLL
    imports VYPER-ABSTRACT-SYNTAX
    imports LLL-ABSTRACT-SYNTAX
    imports VYPER-LLL-UTILS
    imports STRING
    imports K-REFLECTION
    imports KRYPTO


///////////////////////////////////////////////////////////////////////////////
// Configuration / Context
///////////////////////////////////////////////////////////////////////////////


    configuration
    <T>
        <k> #compileVyperToLLL($PGM:Pgm) </k>
        <lll> .K </lll>  // output lll program
        <env> .Map </env>  // In-memory variables. Var |-> TypedAddr
        <nextMem> @reservedMemPos </nextMem>  // Next available memory location
        <global> .Map </global>  // Global variables. Var |-> TypedAddr
        <nextStorage> 0 </nextStorage>
        <internalSig> .Map </internalSig>  // internal ABI objects.   (Event, Func)Name |-> (Event, Func)Record
        <contracts> .Map </contracts>      // external ABI objects. Map from contract names to sets of signatures.
        <currentContract> .K </currentContract> //Current contract, preprocessing phase only.
        <forvar> .Set </forvar>  // Variables defined in for loops, eg. for i in range(6):...
        <return> %void </return>  // Return type of the function
        <constant> false </constant>  // Is the function constant?
        <payable> false </payable>  // Is the function payable?
        <placeholder> 1 </placeholder>  // Number of placeholders generated (used to generate random names)
        <inLoop> .Set </inLoop>  // In Loop status. Whether body is currently evaluating within a for-loop or not.
        <debug> .List </debug>   // Used for debugging
    </T>


///////////////////////////////////////////////////////////////////////////////
// Data Types
///////////////////////////////////////////////////////////////////////////////


    syntax Type        ::= "%mixedT"

    syntax LocTarget   ::= "@storage" | "@memory" | "@storage_prehashed"

    syntax LocAttr     ::= "@locattr" "(" LocTarget "," Bool /*mutable?*/ ")"

    // @none means an LLLExp represents a value rather than a storage/memory location
    syntax LLLExpAttr  ::= LocAttr
                         | "@none"

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
                                                     Int         // size
                                                 ")"

    syntax PackedArgBy32      ::= "@argby32" "(" LLLExps    // code
                                             "," Int        // size
                                             ")"

    syntax PackedArgData      ::= "@argdata" "(" LLLExp      // code
                                             "," Int         // ARGSSTART
                                             "," Int         // size
                                             ")"

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

    syntax KResult  ::= Id
                      | Int
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


    syntax KItem  ::= "#compileVyperToLLL"    "(" Pgm ")"

    syntax KItem  ::= "#compileVyperToLLLAux" "(" CLLLExps /*header code*/  ","
                                                  CLLLExps /*init func*/    ","
                                                  CLLLExps /*regular func*/
                                              ")"                   [seqstrict]

    syntax KItem  ::= "#compileVyperToLLLAux" "(" CLLLExps /*header code*/  ","
                                                  CLLLExps /*regular func*/
                                              ")"                   [seqstrict]
 // ---------------------------------------------------------------------------
    rule #compileVyperToLLL(%pgm(ES, GS, INIT, DEFS, CONTRACTS:Contracts))
         => #addEvents(ES)
            ~> #addGlobals(GS)
            ~> #addFuncs((INIT .Defs) ++Def DEFS ++Def #mkPublicGetters(GS, .Defs))
            ~> #preprocessContracts(CONTRACTS)
            ~> #compileVyperToLLLAux(
                   #initializer_lll,
                   #compileFunc(INIT),
                   #compileFuncs(DEFS ++Def #mkPublicGetters(GS, .Defs), .LLLExps))

    rule #compileVyperToLLL(%pgm(ES, GS, DEFS, CONTRACTS:Contracts))
         => #addEvents(ES)
            ~> #addGlobals(GS)
            ~> #addFuncs(DEFS ++Def #mkPublicGetters(GS, .Defs))
            ~> #preprocessContracts(CONTRACTS)
            ~> #compileVyperToLLLAux(
                   #initializer_lll,
                   #compileFuncs(DEFS ++Def #mkPublicGetters(GS, .Defs), .LLLExps))

    rule <k> #compileVyperToLLLAux(INITIALIZER, INITFUNC, OTHERFUNCS) => . ... </k>
         <lll> _ => $%seq(
                      ($%seq(INITIALIZER),.LLLExps) ++LLL INITFUNC ++LLL
                      ($return(
                         0,
                         $lll($%seq(INITIALIZER ++LLL OTHERFUNCS), 0)),.LLLExps)) </lll>

    rule <k> #compileVyperToLLLAux(INITIALIZER, OTHERFUNCS) => . ... </k>
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

    rule <k> (. => #exception("Duplicate event name: " +String Id2String(NAME))) ~> #addEvent(%event(NAME, _))
         ... </k>
         <internalSig>... NAME |-> _ ...</internalSig>

    rule <k> #addEventAux(EID:Int, NAME, EPARAMS) => . ... </k>
         <internalSig> SIGS => SIGS[NAME <- @event(EID, NAME, EPARAMS)] </internalSig>


    syntax KItem  ::= "#checkEventParams"      "(" EventParams "," Int "," Ids ")"
 // ------------------------------------------------------------------------------
    rule #checkEventParams(.EventParams, TOPICNUM, NAMES) => .
      requires TOPICNUM <=Int 3

    rule #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
        => #checkIndexedEventParamType(T)
        ~> #ifThen(#inIds(NAME, NAMES),
                   #exception("Duplicate function argument name: " +String Id2String(NAME))
                      ~> #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
                  )
        ~> #checkEventParams(EPARAMS, TOPICNUM +Int 1, NAMES ++Id (NAME .Ids))
      requires TOPICNUM <Int 3

    rule (. => #exception("Maximum of 3 topics.")) ~> #checkEventParams(%eparam(_, _, true) _, TOPICNUM, _)
      requires TOPICNUM >=Int 3

    rule #checkEventParams(%eparam(NAME, T, false) EPARAMS, TOPICNUM, NAMES)
        => #ifThen(#inIds(NAME, NAMES),
                   #exception("Duplicate function argument name: " +String Id2String(NAME))
                      ~> #checkEventParams(%eparam(NAME, T, false) EPARAMS, TOPICNUM, NAMES)
                  )
        ~> #checkEventParams(EPARAMS, TOPICNUM, NAMES ++Id (NAME .Ids))


    syntax KItem  ::= "#checkIndexedEventParamType"   "(" Type ")"
 // ------------------------------------------------------------------------------
    rule #checkIndexedEventParamType(%bytesT(L)) => .
      requires L <=Int 32

    rule (. => #exception("Can only log a maximum of 32 bytes at a time.")) ~> #checkIndexedEventParamType(%bytesT(L))
      requires L >Int 32

    rule #checkIndexedEventParamType(T) => .
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

    rule <k> (. => #exception("Cannot declare a persistent variable twice! " +String Id2String(NAME)))
             ~> #addGlobal(%svdecl(NAME, _, _))
         ... </k>
         <global>... %svar(NAME) |-> _ ...</global>

    rule <k> #addGlobalAux(NAME, T:Type) => . ... </k>
         <global> GLOBALS => GLOBALS[%svar(NAME) <- @taddr(T, LOC, @locattr(@storage, true))] </global>
         <nextStorage> LOC => LOC +Int 1 </nextStorage>


// Preprocess Functions
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
            ~> #ifThen(CCONT ==K .K, #checkPrivatePublicMECE(PRIVATE, PUBLIC))
            ~> #addFuncAux(#computeFuncId(FNAME, PARAMS),
                           FNAME,
                           #parseTypeForParams(PARAMS, .Params),
                           #parseType(T, true),
                           CONSTANT, PAYABLE, PRIVATE)
         ... </k>
         <internalSig> SIGS </internalSig>
         <currentContract> CCONT:K </currentContract>
      requires (CCONT =/=K .K) orBool notBool FNAME in_keys(SIGS)

    rule <k> (. => #exception("Duplicate event or function name: " +String Id2String(FNAME)))
             ~> #addFunc(FNAME, _,_,_,_,_,_)
         ...</k>
         <internalSig> SIGS </internalSig>
         <currentContract> .K </currentContract>
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
         <currentContract> .K </currentContract>


    syntax KItem  ::= "#checkFuncParams" "(" Params "," Ids ")"
 // -----------------------------------------------------------
    rule #checkFuncParams(.Params, NAMES) => .

    rule #checkFuncParams(%param(NAME, T) PARAMS, NAMES)
        => #ifThenElse(#inIds(NAME, NAMES),
                       #exception("Duplicate function argument name: " +String Id2String(NAME))
                          ~> #checkFuncParams(%param(NAME, T) PARAMS, NAMES),
                       #checkFuncParams(PARAMS, NAMES ++Id (NAME .Ids))
           )


    syntax KItem  ::= "#checkPrivatePublicMECE" "(" Bool /*private?*/ "," Bool /*public?*/ ")"
 // --------------------------------------------------------------------------------------------
    rule #checkPrivatePublicMECE(false, false) => #exception("Function visibility must be declared.")

    rule #checkPrivatePublicMECE(true, true)
         => #exception("Cannot use public and private decorators on the same function.")

    rule #checkPrivatePublicMECE(false, true) => .
    rule #checkPrivatePublicMECE(true, false) => .


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

    rule #mkPublicGetter(NAME, PARAMS, T:BaseType, VAR, DEPTH) => #mkPublicGetterBase(NAME, PARAMS, T, VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, T:ByteArrayType, VAR, DEPTH)
        => #mkPublicGetterByteArray(NAME, PARAMS, T, VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, T:ListType, VAR, DEPTH)
        => #mkPublicGetterListT(NAME, PARAMS, T, VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, T:MappingType, VAR, DEPTH)
        => #mkPublicGetterMapT(NAME, PARAMS, T, VAR, DEPTH)

    rule #mkPublicGetter(NAME, PARAMS, T:StructType, VAR, DEPTH)
        => #mkPublicGetterStructT(NAME, PARAMS, T, VAR, DEPTH)


    syntax Defs  ::= "#mkPublicGetterBase"      "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterByteArray" "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterListT"     "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterMapT"      "(" String "," Params "," Type "," Var "," Int ")"  [function]
    syntax Defs  ::= "#mkPublicGetterStructT"   "(" String "," Params "," Type "," Var "," Int ")"  [function]
 // -------------------------------------------------------------------------------------------------------------
    rule #mkPublicGetterBase(NAME, PARAMS, T, VAR, DEPTH)
        => %fdecl(%@public %@constant .Decorators,
                  String2Id(NAME),
                  PARAMS,
                  T,
                  %return(VAR) .Stmts) .Defs

    rule #mkPublicGetterByteArray(NAME, PARAMS, %bytesT(L), VAR, DEPTH)
        => %fdecl(%@public %@constant .Decorators,
                  String2Id(NAME),
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


// Preprocess Contracts
// =============

    syntax K ::= "#preprocessContracts" "(" Contracts ")"
 // -------------------------------------------------------------------------------------------------------------

    rule <k> (. => #addFuncs(DEFS))
             ~> #preprocessContracts(%contract(CID:Id, DEFS:Defs) CS:Contracts => CS) ...</k>
         <currentContract> _ => CID </currentContract>
         <contracts> CIDS => CIDS[CID <- .Map] </contracts>
      requires notBool CID in keys(CIDS)

    rule <k> (. => #exception("Duplicate contract name: " +String Id2String(CID)))
             ~> #preprocessContracts(%contract(CID:Id, DEFS:Defs) CS:Contracts) ...</k>
         <contracts>... CID |-> _ ...</contracts>

    rule #preprocessContracts(.Contracts) => .

    rule <k> #addFuncAux(FID:Int, FNAME, PARAMS, T, CONSTANT, PAYABLE, PRIVATE) => . ... </k>
         <contracts>... CID |-> ( SIGS => SIGS[FNAME <- @func(FID, FNAME, PARAMS, T, CONSTANT, PAYABLE, PRIVATE)
                                                ])
         ...</contracts>
         <currentContract> CID:Id </currentContract>


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
            => #clearConfig
            ~> #compileFuncAux(#copyArg(PARAMS, #isInitFunc(FNAME)),
                               #addClampersForDecorators(PAYABLE, PRIVATE),
                               #fillParams(PARAMS, 0, #isInitFunc(FNAME), .LLLExps),
                               #compileStmts(STMTS, .LLLExps),
                               FUNCID,
                               #isInitFunc(FNAME))
         ... </k>
         <internalSig>... FNAME |-> @func(FUNCID, FNAME, PARAMS, RT, CONSTANT, PAYABLE, PRIVATE) ...</internalSig>
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

    rule #mkClamper(_:AddressType, DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), $mload(@addrSizePos)),.LLLExps

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
    rule <k> #clearConfig => . ...</k>
         <env> _ => .Map </env>
         <nextMem> _ => @reservedMemPos </nextMem>
         <forvar> _ => .Set </forvar>
         <placeholder> _ => 1 </placeholder>
         <inLoop> _ => .Set </inLoop>


///////////////////////////////////////////////////////////////////////////////
// Stmts
///////////////////////////////////////////////////////////////////////////////


    syntax CLLLExps  ::= "#compileStmts" "(" Stmts "," LLLExps ")"
 // --------------------------------------------------------------
    rule #compileStmts(STMT STMTS, RESULTCODE) => #compileStmt(STMT) ~> #compileStmts(STMTS, RESULTCODE)

    rule (STMTCODE:LLLExps ~> #compileStmts(STMTS, RESULTCODE))
        => #compileStmts(STMTS, RESULTCODE ++LLL STMTCODE)

    rule #compileStmts(.Stmts, RESULTCODE) => RESULTCODE


    syntax CLLLExps  ::= "#compileStmt" "(" Stmt ")"
 // ------------------------------------------------


// Annotated Assignment
// ====================


    rule #compileStmt(%annvar(NAME, T)) => #newVar(NAME, #parseType(T, true)) ~> #deletePrev ~> $pass,.LLLExps

    rule #compileStmt(%annvar(NAME, T, EXPR))
         => #newVar(NAME, #parseType(T, true)) ~> #deletePrev ~> #compileStmt(%assign(%var(NAME), EXPR))

    //Delete the KResult item in front of #deletePrev, and the #deletePrev.
    syntax K ::= "#deletePrev"
 // ---------------------------------------------------------------------------
    rule _:KResult ~> #deletePrev => .


// Assignment
// ==========


    rule #compileStmt(%assign(V, E)) => #assign(V, #compileToLoc(E))


    syntax CLLLExps  ::= "#assign"    "(" Var                             ","
                                          CTypedLLLExp  /*compiled Expr*/
                                      ")"                         [strict(2)]
 // ---------------------------------------------------------------------------
    rule #assign(V, @tlll(T, CODE, EXPRATTR))
        => #assignImpl(#getTarget(V, #lookupOrNewVar(V, T)),
                      @tlll(T, CODE, EXPRATTR))
      requires T =/=K %NoneType


    /*  Checks that var is not used in a loop, then makes some more checks inside #getTargetAux(), 
        then rewrites into arg 2*/
    syntax CTypedLLLExp  ::= "#getTarget" "(" Var ","       //raw var 
                                              CTypedLLLExp  //same var compiled to TypedLLLExp. 
                                          ")"  [strict(2)]
 // -------------------------------------------------------------------------------
    rule <k> (. => #exception("Altering iterator which is in use!"))
             ~> #getTarget(%var(NAME), _) ... </k>
         <forvar>... SetItem(NAME) ...</forvar>

    rule <k> #getTarget(%var(NAME), TCODE:TypedLLLExp) => #getTargetAux(TCODE) ... </k>
         <forvar> FORVARS </forvar>
      requires notBool NAME in FORVARS

    rule #getTarget(%svar(_), TCODE:TypedLLLExp) => #getTargetAux(TCODE)

    rule #getTarget(%attribute(_,_), TCODE:TypedLLLExp) => #getTargetAux(TCODE)

    rule <k> (. => #exception("Altering list while being iterated!"))
             ~> #getTarget(%subscript(V, _), _) ... </k>
         <inLoop>... SetItem(V) ...</inLoop>

    rule <k> #getTarget(%subscript(V, _), TCODE) => #getTargetAux(TCODE) ... </k>
         <inLoop> INLOOP </inLoop>
      requires notBool V in INLOOP


    //Performs a number of checks then rewrites into the argument.
    syntax CTypedLLLExp  ::= "#getTargetAux" "(" TypedLLLExp ")"
 // -------------------------------------------------------------------------------
    rule <k> #getTargetAux(@tlll(T, LOC, @locattr(TARGET, MUTABLE)))
            => #ifThen(TARGET ==K @storage andBool CONSTANT ==K true,
                       #exception("Cannot modify storage inside a constant function!")
                          ~> #getTargetAux(@tlll(T, LOC, @locattr(TARGET, MUTABLE)))
                      )
            ~> #ifThen(MUTABLE ==K false,
                       #exception("Cannot modify function argument")
                          ~> #getTargetAux(@tlll(T, LOC, @locattr(TARGET, MUTABLE)))
                      )
            ~> @tlll(T, LOC, @locattr(TARGET, MUTABLE))
         ... </k>
         <constant> CONSTANT </constant>


    /*  Assignment expression: V = E. 
        After all checks have been performed and memory was allocated.

        Also represents make_setter() from Viper compiler.
    */
    syntax CLLLExps  ::= "#assignImpl" "(" CTypedLLLExp  /*left variable loc*/   ","
                                           CTypedLLLExp  /*right compiled Expr*/ ")"  [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #assignImpl(@tlll(LT:BaseType, LOC, LOCATTR), RTCODE)
        => #mkSetterBase(@tlll(LT, LOC, LOCATTR),
                         #baseTypeConvert(RTCODE, LT))

    rule #assignImpl(@tlll(LT:ByteArrayType, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
        => #ifThenElse(notBool(isByteArrayType(RT)),
                       #exception("Setter type mismatch: left side is byte array but right side is not.")
                          ~> #assignImpl(@tlll(LT:ByteArrayType, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR)),
                       #mkByteArrayCopier(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
           )

    // Can't copy mappings
    rule (. => #exception("Cannot copy mappings; can only copy individual elements."))
         ~> #assignImpl(@tlll(LT:MappingType, LOC, LOCATTR), RTCODE)

    rule #assignImpl(@tlll(LT:ListType, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
        => #ifThenElse(notBool(isListType(RT)),
                       #exception("Setter type mismatch: left side is array but right side is not.")
                          ~> #assignImpl(@tlll(LT:ListType, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR)),
                       #assignList(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
           )

    rule #assignImpl(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
        => #ifThenElse(getKLabel(LT) =/=K getKLabel(RT),
                       #exception("Setter type mismatch: left side is struct or tuple, right side has different form.")
                          ~> getKLabel(LT) ~> "vs" ~> getKLabel(RT)
                          ~> #assignImpl(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR)),
                       #assignStructOrT(@tlll(LT, LOC, LOCATTR), @tlll(RT, CODE, EXPRATTR))
           )
      requires isStructType(LT) orBool isTupleType(LT)


    // Basic Types
    syntax CLLLExps  ::= "#mkSetterBase"  "(" TypedLLLExp "," CTypedLLLExp ")"  [strict(2)]
 // ---------------------------------------------------------------------------------------
    rule #mkSetterBase(@tlll(_, LOC, @locattr(@storage, _)), @tlll(_, CODE, _))
        => $sstore(LOC, CODE),.LLLExps

    rule #mkSetterBase(@tlll(_, LOC, @locattr(@memory, _)), @tlll(_, CODE, _))
        => $mstore(LOC, CODE),.LLLExps


    // foo = [1, 2, 3] : Assign entire lists.
    syntax CLLLExps  ::= "#assignList" "(" TypedLLLExp "," TypedLLLExp ")"

    syntax CLLLExps  ::= "#assignListAux" "(" TypedLLLExp ","  // left
                                              TypedLLLExp ","  // left token
                                              TypedLLLExp      // right
                                          ")"
 // ------------------------------------------------------------
    rule #assignList(@tlll(LT, LCODE, @locattr(LTARGET, LMUTABLE)), @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(#getListTCount(LT) =/=K #getListTCount(RT),
                   #exception("Mismatched number of elements in left and right side arrays.")
                      ~> #assignList(@tlll(LT, LCODE, @locattr(LTARGET, LMUTABLE)), @tlll(RT, RCODE, REXPRATTR))
           )
        ~> #ifThenElse(LTARGET ==K @storage,
                       #assignListAux(@tlll(LT, $sha3_32(LCODE), @locattr(@storage_prehashed, LMUTABLE)),
                                      @tlll(LT, $_L, @locattr(@storage_prehashed, LMUTABLE)),
                                      @tlll(RT, RCODE, REXPRATTR)),
                       #assignListAux(@tlll(LT, LCODE, @locattr(LTARGET, LMUTABLE)),
                                      @tlll(LT, $_L, @locattr(LTARGET, LMUTABLE)),
                                      @tlll(RT, RCODE, REXPRATTR)))

    rule #assignListAux(@tlll(LT, LCODE, _), LTTOKENCODE, @tlll(RT, RCODE, REXPRATTR))
        => #assignListLiteral(LT, LCODE, LTTOKENCODE, 0, RCODE, .LLLExps)
      requires isMultiLLLExp(RCODE)

    rule #assignListAux(@tlll(LT:Type, LCODE, _), LTTOKENCODE, @tlll(RT, RCODE, RLOCATTR))
        => #assignListVar(LT, LCODE, LTTOKENCODE, 0, RCODE,
                          @tlll(RT, $_R, RLOCATTR), .LLLExps)
      requires notBool isMultiLLLExp(RCODE)


    syntax CLLLExps  ::= "#assignListLiteral" "(" Type         ","  // left list type
                                                  LLLExp       ","  // left code
                                                  TypedLLLExp  ","  // left token
                                                  Int          ","  // index
                                                  LLLExp       ","  // right code
                                                  LLLExps           // result code
                                              ")"
 // -------------------------------------------------------------------------------
    rule #assignListLiteral(%listT(SUBTYPE, N), LCODE, LTTOKENCODE, INDEX, $multi(TEXPR TEXPRS), RESULTCODE)
        => #assignImpl(#lookupVarElement(LTTOKENCODE, @tlll(%num, INDEX, @none)), TEXPR)
        ~> #assignListLiteral(%listT(SUBTYPE, N), LCODE, LTTOKENCODE, INDEX, $multi(TEXPRS), RESULTCODE)
      requires INDEX <Int N

    rule #assignListLiteral(%listT(SUBTYPE, N), LCODE, _, INDEX, _, RESULTCODE)
        => $with($_L, LCODE, $%seq(RESULTCODE)),.LLLExps
      requires INDEX ==Int N

    rule CODE:LLLExps ~> #assignListLiteral(LT, LCODE, LTTOKENCODE, INDEX, RCODE, RESULTCODE)
        => #assignListLiteral(LT, LCODE, LTTOKENCODE, INDEX +Int 1, RCODE, RESULTCODE ++LLL CODE)


    syntax CLLLExps  ::= "#assignListVar" "(" Type        ","  // left list type
                                              LLLExp      ","  // left code
                                              TypedLLLExp ","  // left token
                                              Int         ","  // index
                                              LLLExp      ","  // right code
                                              TypedLLLExp ","  // right token
                                              CLLLExps         // result code
                                          ")"           [strict(7)]
  // --------------------------------------------------------------------------------
    rule #assignListVar(%listT(SUBTYPE, N:Int), LCODE, LTOKEN:TypedLLLExp, INDEX => INDEX +Int 1,
                        RCODE, RTOKEN:TypedLLLExp,
                        RESULTCODE:LLLExps
                        => #seq(RESULTCODE,
                                #assignImpl(#lookupVarElement(LTOKEN, @tlll(%num, INDEX, @none)),
                                            #lookupVarElement(RTOKEN, @tlll(%num, INDEX, @none))))
         )
       requires INDEX <Int N

    rule #assignListVar(%listT(SUBTYPE, N:Int), LCODE, _, INDEX, RCODE, _, RESULTCODE:LLLExps)
         => $with($_L, LCODE, $with($_R, RCODE, $%seq(RESULTCODE))),.LLLExps
       requires INDEX ==Int N


    // Struct
    syntax CLLLExps  ::= "#assignStructOrT" "(" TypedLLLExp "," TypedLLLExp ")"

    syntax CLLLExps  ::= "#assignStructOrTAux" "(" TypedLLLExp ","  // left
                                                   TypedLLLExp ","  // left token
                                                   TypedLLLExp ")"  // right
 // ---------------------------------------------------------------------------
    rule #assignStructOrT(@tlll(LT:Type, LCODE, @locattr(LTARGET, LMUTABLE)),
                          @tlll(RT, RCODE, REXPRATTR))
        => #checkStructOrTAssignValid(LT, RT)
        ~> #ifThenElse(LTARGET ==K @storage,
                       #assignStructOrTAux(@tlll(LT, $sha3_32(LCODE), @locattr(@storage_prehashed, LMUTABLE)),
                                           @tlll(LT, $_L, @locattr(@storage_prehashed, LMUTABLE)),
                                           @tlll(RT, RCODE, REXPRATTR)),
                       #assignStructOrTAux(@tlll(LT, LCODE, @locattr(LTARGET, LMUTABLE)),
                                           @tlll(LT, $_L, @locattr(LTARGET, LMUTABLE)),
                                           @tlll(RT, RCODE, REXPRATTR)))

    rule #assignStructOrTAux(@tlll(LT:Type, LCODE, _), LTTOKENCODE, @tlll(RT, RCODE:MultiLLLExp, REXPRATTR))
        => #assignStructOrTLiteral(LT, LCODE, LTTOKENCODE, RCODE, 0, .LLLExps)

    rule #assignStructOrTAux(@tlll(LT:Type, LCODE, _), LTTOKENCODE, @tlll(RT, RCODE, RLOCATTR))
        => #assignStructOrTVar(LT, LCODE, LTTOKENCODE, RCODE,
                               @tlll(RT, $_R, RLOCATTR), 0, .LLLExps)
      requires notBool isMultiLLLExp(RCODE)


    syntax KItem  ::= "#checkStructOrTAssignValid" "(" Type "," Type ")"
 // -----------------------------------------------------------------------

    //%structT()
    rule #checkStructOrTAssignValid(%structT(%annvar(NAME, _) LANNVARS => LANNVARS),
                                    %structT(%annvar(NAME, _) RANNVARS => RANNVARS))

    rule #checkStructOrTAssignValid(%structT(.AnnVars), %structT(.AnnVars)) => .

    rule (. => #exception("Keys don't match for structs."))
         ~> #checkStructOrTAssignValid(%structT(%annvar(LNAME, _) LANNVARS),
                                       %structT(%annvar(RNAME, _) RANNVARS))
      requires LNAME =/=K RNAME

    rule (. => #exception("Keys don't match for structs."))
         ~> #checkStructOrTAssignValid(%structT(%annvar(_,_) _), %structT(.AnnVars))

    rule (. => #exception("Keys don't match for structs."))
         ~> #checkStructOrTAssignValid(%structT(.AnnVars), %structT(%annvar(_,_) _))

    //%tupleT()
    rule #checkStructOrTAssignValid(%tupleT(_:Type Ts1 => Ts1),
                                    %tupleT(_:Type Ts2 => Ts2))

    rule #checkStructOrTAssignValid(%tupleT(.Types), %tupleT(.Types)) => .

    rule (. => #exception("Tuple lengths don't match."))
         ~> #checkStructOrTAssignValid(%tupleT(_:Type _), %tupleT(.Types))

    rule (. => #exception("Tuple lengths don't match."))
         ~> #checkStructOrTAssignValid(%tupleT(.Types), %tupleT(_:Type _))


    syntax CLLLExps  ::= "#assignStructOrTLiteral" "("  Type        ","  // LHS type
                                                        LLLExp      ","  // left code
                                                        TypedLLLExp ","  // left token
                                                        LLLExp      ","  // right code
                                                        Int         ","  // counter
                                                        LLLExps          // result code
                                                    ")"
 // ------------------------------------------------------------------
    //struct
    rule (. => #assignImpl(#lookupVarElement(LTTOKENCODE, @tlll(%void, NAME, @none)), TEXPR))
         ~> #assignStructOrTLiteral(%structT(%annvar(NAME, T) ANNVARS => ANNVARS),
                                    LCODE, LTTOKENCODE, $multi(TEXPR TEXPRS => TEXPRS), 0, RESULTCODE)

    //tuple
    rule (. => #assignImpl(#lookupVarElement(LTTOKENCODE, @tlll(%void, CNT, @none)), TEXPR))
         ~> #assignStructOrTLiteral(%tupleT(_),
                                    LCODE, LTTOKENCODE, $multi(TEXPR TEXPRS => TEXPRS), CNT:Int => CNT +Int 1, RESULTCODE)

    rule (CODE:LLLExps => .)
         ~> #assignStructOrTLiteral(LT:Type, LCODE, LTTOKENCODE, RCODE, _, RESULTCODE => RESULTCODE ++LLL CODE)

    rule #assignStructOrTLiteral(LT:Type, LCODE, _, _, _, RESULTCODE)
        => $with($_L, LCODE, $%seq(RESULTCODE)), .LLLExps
      requires LT ==K %structT(.AnnVars) orBool LT ==K %tupleT(.Types)

    syntax CLLLExps  ::= "#assignStructOrTVar" "(" Type        ","  // LHS type
                                                   LLLExp      ","  // left code
                                                   TypedLLLExp ","  // left token
                                                   LLLExp      ","  // right code
                                                   TypedLLLExp ","  // right token
                                                   Int         ","  // counter
                                                   LLLExps     ")"  // result code
 // -------------------------------------------------------------
    //struct
    rule (. => #assignImpl(#lookupVarElement(LTTOKENCODE, @tlll(%void, NAME, @none)),
                           #lookupVarElement(RTTOKENCODE, @tlll(%void, NAME, @none))))
         ~> #assignStructOrTVar(%structT(%annvar(NAME, T) ANNVARS => ANNVARS),
                                LCODE, LTTOKENCODE, RCODE, RTTOKENCODE, 0, RESULTCODE)

    //tuple
    rule (. => #assignImpl(#lookupVarElement(LTTOKENCODE, @tlll(%void, CNT, @none)),
                           #lookupVarElement(RTTOKENCODE, @tlll(%void, CNT, @none))))
         ~> #assignStructOrTVar(%tupleT(_),
                                LCODE, LTTOKENCODE, RCODE, RTTOKENCODE, CNT:Int, RESULTCODE)

    rule (CODE:LLLExps => .)
         ~> #assignStructOrTVar(LT:Type, LCODE, LTTOKENCODE, RCODE, _, RTTOKENCODE, RESULTCODE => RESULTCODE ++LLL CODE)

    rule #assignStructOrTVar(LT:Type, LCODE, _, RCODE, _, _, RESULTCODE)
        => $with($_L, LCODE, $with($_R, RCODE, $%seq(RESULTCODE))),.LLLExps
      requires LT ==K %structT(.AnnVars) orBool LT ==K %tupleT(.Types)


// Aug Assignment
// ==============


    rule #compileStmt(%augassign(OP, V, E)) => #augassign(OP,
                                                          #getTarget(V, #compileLocExpr(V)),
                                                          #compileToVal(E))


    syntax CLLLExps  ::= "#augassign"    "(" AugAssignOp  ","
                                             CTypedLLLExp ","  // variable loc
                                             CTypedLLLExp      // compiled expr
                                         ")"  [seqstrict(2,3)]

    syntax CLLLExps  ::= "#augassignAux" "(" AugAssignOp  ","
                                             CTypedLLLExp ","
                                             TypedLLLExp  ")"
 // ---------------------------------------------------------
    rule #augassign(OP, @tlll(LT:BaseType, LOC, @locattr(TARGET, MUTABLE)), RTCODE)
        => #augassignAux(OP, @tlll(LT, LOC, @locattr(TARGET, MUTABLE)), RTCODE)

    rule (. => #exception("Can only use aug-assign operators with simple types!"))
         ~> #augassign(OP, @tlll(LT, LOC, @locattr(TARGET, MUTABLE)), RTCODE)
      requires notBool isBaseType(LT)

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

    syntax CLLLExps  ::= "#desugarAugAssignAux" "(" LLLExp       ","  /*loc*/
                                                    LocTarget    ","
                                                    CTypedLLLExp
                                                ")"      [strict(3)]
 // ----------------------------------------------------------------
    rule #desugarAugAssign(@tlll(LT, LOC, @locattr(TARGET, MUTABLE)), RTCODE:TypedLLLExp)
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
        => #ifstmt(#compileToVal(TEST),
                   #compileStmts(THENSTMTS, .LLLExps),
                   #compileStmts(ELSESTMTS, .LLLExps))

    rule #compileStmt(%if(TEST, THENSTMTS)) => #ifstmt(#compileToVal(TEST), #compileStmts(THENSTMTS, .LLLExps))

    rule #ifstmt(@tlll(_, CODE, _), THEN:LLLExps, ELSE:LLLExps) => $if(CODE, $%seq(THEN), $%seq(ELSE)),.LLLExps

    rule #ifstmt(@tlll(_, CODE, _), THEN:LLLExps) => $if(CODE, $%seq(THEN)),.LLLExps


// For Loop
// ========

// for in range
//-------------------------

    // e.g. for i in range(10): ...
    rule #compileStmt(%forrange(ITER, ROUNDS, STMTS) => %forrange(ITER, 0, ROUNDS, STMTS))

    // e.g. for i in range(100, 110): ...
    rule #compileStmt(%forrange(ITER, START:Int, END:Int, STMTS))
        => #forrange(#newLoopVar(ITER, %num), @tlll(%num, START, @none), END -Int START, #compileStmts(STMTS, .LLLExps))
        ~> #clearIter(ITER)

    // e.g. for i in range(x, x + 10): ...
    rule #compileStmt(%forrange(ITER, %var(V), %binop(+, %var(V), ROUNDS:Int), STMTS))
        => #forrange(#newLoopVar(ITER, %num), #compileToVal(%var(V)), ROUNDS, #compileStmts(STMTS, .LLLExps))
        ~> #clearIter(ITER)


    syntax CLLLExps  ::= "#forrange" "(" CTypedLLLExp ","
                                         CTypedLLLExp ","  // start
                                         Int          ","  // rounds
                                         CLLLExps          // body code
                                     ")"  [seqstrict(1,2,4)]
 // --------------------------------------------------------
    rule #forrange(@tlll(%num, LOC:Int, _), @tlll(_, STARTCODE, _), ROUNDS, BODYCODE:LLLExps)
        => $repeat(LOC, STARTCODE, ROUNDS, $%seq(BODYCODE)),.LLLExps


// for in list
//-------------------------

    /*
    Desugaring for over expr into for over var:
        for a in exp: block
    =>
        list = exp
        for a in list: block
    */
    rule #compileStmt(%forlist(ITER, EXPR, STMTS)) => #forlistNonVar(ITER, EXPR, STMTS, #newVarId)
    requires notBool isVar(EXPR)

    syntax CLLLExps  ::= "#forlistNonVar" "(" Id           "," // loop iterator
                                              Expr         "," // list expr
                                              Stmts        "," // loop statements
                                              K                // temp var - the list
                                          ")"                  [strict(4)]
  // ---------------------------------------------------------
    rule #forlistNonVar(ITER, EXPR, STMTS, ListId:Id)
         => #compileStmts((
                %assign(%var(ListId), EXPR)
                %forlist(ITER, %var(ListId), STMTS)),
                .LLLExps
            )


    // e.g. for i in list(): ...
    rule #compileStmt(%forlist(ITER, VAR:Var, STMTS))
        => #forlist(ITER, VAR, #compileToLoc(VAR), STMTS)

    syntax CLLLExps  ::= "#forlist" "(" Id           "," // loop iterator
                                        Var          "," // list expr
                                        CTypedLLLExp "," // list expr, compiled
                                        Stmts            // loop statements
                                    ")"    [strict(3)]

 // ---------------------------------------------------------
    rule #forlist(ITER:Id, VAR:Var, @tlll(%listT(SUBTYPE:Type, N), CODE, EXPRATTR), STMTS:Stmts)
        => #ifThen(notBool(isBaseType(SUBTYPE)),
                   #exception("For loops allowed only on basetype lists.")
                      ~> #forlist(ITER:Id, VAR:Var, @tlll(%listT(SUBTYPE:Type, N), CODE, EXPRATTR), STMTS:Stmts)
           )
        ~> #setInLoop(VAR)
        ~> #forlistVar(#newLoopVar(ITER, SUBTYPE),
                       #newVar(String2Id("_index_for_" +String Id2String(ITER)), %num),
                       @tlll(%listT(SUBTYPE, N), CODE, EXPRATTR),
                       #compileStmts(STMTS, .LLLExps))
        ~> #removeInLoop(VAR)
        ~> #clearIter(ITER)
        ~> #clearVar(String2Id("_index_for_" +String Id2String(ITER)))


    syntax CLLLExps  ::= "#forlistVar" "("      CTypedLLLExp  ","  // iterator var - value in list
                                                CTypedLLLExp  ","  // index var - position in list
                                                TypedLLLExp   ","  // list var - variable storing the list literal
                                                CLLLExps           // for body
                                       ")"      [seqstrict(1,2,4)]
 // ------------------------------------------------------------------------------------------
    // List allocated in memory
    rule #forlistVar(@tlll(_, ITERLOC, _),
                          @tlll(_, INDEXLOC, _),
                          @tlll(%listT(SUBTYPE, N), LISTLOC, @locattr(@memory, _)),
                          BODYCODE)
        => $repeat(INDEXLOC, 0, N, $%seq(
                                     $mstore(ITERLOC, $mload($add(LISTLOC, $mul($mload(INDEXLOC), 32)))),
                                     $%seq(BODYCODE),.LLLExps)),.LLLExps

    // List allocated in storage
    rule #forlistVar(@tlll(_, ITERLOC, _),
                          @tlll(_, INDEXLOC, _),
                          @tlll(%listT(SUBTYPE, N), LISTLOC, @locattr(@storage, _)),
                          BODYCODE)
        => $%seq(
             $repeat(INDEXLOC, 0, N, $%seq(
                                       $mstore(ITERLOC, $sload($add($sha3_32(LISTLOC), $mload(INDEXLOC)))),
                                       $%seq(BODYCODE),.LLLExps)),.LLLExps),.LLLExps


    //sequence of statements to be concatenated
    syntax CLLLExps ::= "#seq" "(" CLLLExps "," CLLLExps ")" [seqstrict]
    // ------------------------------------------
    rule #seq(CODE1:LLLExps, CODE2:LLLExps) => $%seq(CODE1 ++LLL CODE2),.LLLExps


    //sequence of statements to be concatenated, followed by an expression
    syntax CTypedLLLExps ::= "#exprSeq" "(" CLLLExps "," CTypedLLLExp ")" [seqstrict]
    // ------------------------------------------
    rule #exprSeq(CODE1:LLLExps, @tlll(T, CODE2, EXPRATTR)) => @tlll(T, $%seq(CODE1 ++LLL CODE2), EXPRATTR)


    syntax KItem  ::= "#setInLoop" "(" Var ")"
 // ------------------------------------------
    rule <k> #setInLoop(VAR) => . ... </k>
         <inLoop>... (.Set => SetItem(VAR)) ...</inLoop>


    syntax KItem  ::= "#removeInLoop" "(" Var ")"
 // ---------------------------------------------
    rule <k> CODE:LLLExps ~> (#removeInLoop(VAR) => .) ... </k>
         <inLoop>... (SetItem(VAR) => .Set) ...</inLoop>


    // deletes the variable from <env> and <forvar>
    syntax KItem  ::= "#clearIter" "(" Id ")"
 // -------------------------------------------------
    rule <k> CODE:LLLExps ~> (#clearIter(ITER:Id) => .) ... </k>
         <env>... (%var(ITER) |-> _ => .Map) ...</env>
         //K bug: in this format rule gets stuck when <forvar> has 2 entries See test_repeater.py test 3.
         //<forvar> (SetItem(%var(ITER)) => .Set) FORVARS </forvar>
         <forvar>... SetItem(ITER) => .Set ...</forvar>


// Break
// =====


    rule #compileStmt(%break) => $break,.LLLExps


// Pass
// =====


    rule #compileStmt(%pass)  => $pass,.LLLExps


// Return
// ======


    rule <k> #compileStmt(%return) => #ifThenElse(T =/=K %void,
                                                  #exception("Expecting to return a value") ~> #compileStmt(%return),
                                                  ($return(0, 0),.LLLExps)) ... </k>
         <return> T </return>

    rule <k> #compileStmt(%return(E)) => #ifThenElse(T =/=K %void,
                                                     #return(#compileToVal(E), T),
                                                     #exception("Not expecting to return a value")
                                                        ~> #compileStmt(%return(E))) ... </k>
         <return> T </return>


    syntax CLLLExps  ::= "#return" "(" CTypedLLLExp "," Type /*return type*/ ")"  [strict(1)]
 // -----------------------------------------------------------------------------------------
    // Return Base Type
    rule (. => #exception("Trying to return base type but output expecting non base type."))
         ~> #return(@tlll(T:BaseType, CODE, EXPRATTR), RETURNTYPE)
      requires notBool isBaseType(RETURNTYPE)

    rule #return(@tlll(T:BaseType, CODE, EXPRATTR), RETURNTYPE:BaseType)
         => #returnBase(@tlll(T, CODE, EXPRATTR), RETURNTYPE)

    // Return Byte Array Type
    rule #return(@tlll(T:ByteArrayType, CODE, EXPRATTR), RETURNTYPE)
         => #ifThenElse(notBool(isByteArrayType(RETURNTYPE)),
                        #exception("Trying to return byte array type but it is not matching the expected return type.")
                          ~> #return(@tlll(T:ByteArrayType, CODE, EXPRATTR), RETURNTYPE),
                        #returnBytesT(@tlll(T, CODE, EXPRATTR), RETURNTYPE))

    rule (. => #exception("Return list length doesn't match the expected length."))
         ~> #return(@tlll(%listT(SUBTYPE1, N1), CODE, EXPRATTR), %listT(SUBTYPE2, N2))
      requires N1 =/=Int N2

    syntax CLLLExps  ::= "#returnBase"    "(" TypedLLLExp "," Type ")"
    syntax CLLLExps  ::= "#returnBaseAux" "(" TypedLLLExp "," Type ")"
 // ------------------------------------------------------------------
    rule #returnBase(@tlll(T, CODE, EXPRATTR), RETURNTYPE)
        => #ifThenElse(#areUnitsCompatible(T, RETURNTYPE, #isNumLiteral(CODE)),
                       #returnBaseAux(@tlll(#dropUnit(T), CODE, EXPRATTR), #dropUnit(RETURNTYPE)),
                       #exception("Return type units mismatch") ~> #returnBase(@tlll(T, CODE, EXPRATTR), RETURNTYPE))

    rule #returnBaseAux(@tlll(T, CODE, LA), RETURNTYPE)
        => #ifThenElse((T ==K RETURNTYPE) orBool (T ==K %num andBool RETURNTYPE ==K %signed256),
                       $%seq($mstore(0, CODE), $return(0, 32),.LLLExps),.LLLExps,
                       #exception("Unsupported type conversion.") ~> #returnBaseAux(@tlll(T, CODE, LA), RETURNTYPE))


    syntax CLLLExps  ::= "#returnBytesT"    "(" TypedLLLExp "," Type ")"
    syntax CLLLExps  ::= "#returnBytesTAux" "(" TypedLLLExp ")"
 // -----------------------------------------------------------------------
    rule #returnBytesT(@tlll(%bytesT(L1), CODE, LOCATTR), %bytesT(L2))
        => #ifThenElse(L1 >Int L2,
                       #exception("Cannot cast from greater max-length to shorter max-length.")
                          ~> #returnBytesT(@tlll(%bytesT(L1), CODE, LOCATTR), %bytesT(L2)),
                       #returnBytesTAux(@tlll(%bytesT(L1), CODE, LOCATTR)))

    rule #returnBytesTAux(@tlll(%bytesT(L), CODE, @locattr(@memory, _)))
        => $with(
             $_loc, // _loc = CODE
             CODE,
             $%seq(
                //*(_loc-32) = 32
                // Why this memory region is used, instead of _loc to _loc+32 ??
               $mstore($sub($_loc, 32), 32),
                //return bytes from _loc-32 of length: *(_loc) + 64
                //value on _loc represents the size of byte array.
                //Value on _loc+32 represents first (and in this implementation the only) 32 bytes of the byte array.
                //fixme (not here, byte array read rule) only 32 bytes are read regardless of actual byte array size.
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


    // Return List Type
    //-------------------
    rule #return(@tlll(%listT(SUBTYPE1, N), CODE, EXPRATTR), %listT(SUBTYPE2, N))
        => #returnListT(@tlll(%listT(SUBTYPE1, N), CODE, EXPRATTR), %listT(SUBTYPE2, N))

    syntax CLLLExps  ::= "#returnListT" "(" TypedLLLExp "," //returned value
                                            Type            //expected type
                                        ")"
 // -------------------------------------------------------
    rule #returnListT(@tlll(%listT(SUBTYPE1, N), CODE, EXPRATTR), %listT(SUBTYPE2, N))
        => #ifThenElse(#isInMemory(EXPRATTR) andBool (SUBTYPE1 ==K SUBTYPE2) andBool notBool isMultiLLLExp(CODE),
                       ($return(CODE, #sizeOfType(%listT(SUBTYPE2, N))), .LLLExps),
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
        => #returnListTByCopyAux(#assignImpl(@tlll(T, LOC, LOCATTR), TCODE),
                               LOC, RETURNTYPE)

    rule #returnListTByCopyAux(SETTER, LOC, RETURNTYPE)
        => $%seq(SETTER ++LLL ($return(LOC, #sizeOfType(RETURNTYPE)),.LLLExps)),.LLLExps


// Return Tuple
// ===============================

    /*  //sub = returned value, 1st arg of #return

        subs = []
        dynamic_offset_counter = LLLnode(self.context.get_next_mem(), typ=None, annotation="dynamic_offset_counter")  # dynamic offset position counter.
        new_sub = LLLnode.from_list(self.context.get_next_mem() + 32, typ=self.context.return_type, location='memory', annotation='new_sub')
        keyz = list(range(len(sub.typ.members)))
        dynamic_offset_start = 32 * len(sub.args)  # The static list of args end.
        left_token = LLLnode.from_list('_loc', typ=new_sub.typ, location="memory")
            e.g. left_token == $_loc
    */
    rule <k> #return(@tlll(%tupleT(Ts1:Types), CODE, EXPRATTR), %tupleT(Ts2:Types))
             => #checkStructOrTAssignValid(%tupleT(Ts1), %tupleT(Ts2))
             ~> #returnTupleT(@tlll(%tupleT(Ts1), CODE, EXPRATTR),
                              NextMem, NextMem +Int 32, 32 *Int #listLen(Ts1, 0), 0, .LLLExps)
         ...</k>
         <nextMem> NextMem </nextMem>

    syntax Int ::= #listLen( Types , Int )  [function]
    rule #listLen(_:Type Ts => Ts, I => I +Int 1)
    rule #listLen(.Types, I) => I

    syntax CLLLExps ::= "#returnTupleT" "(" TypedLLLExp   // return value. Also stores keyz.
                                        "," Int           // dynamic_offset_counter
                                        "," Int           // new_sub
                                        "," Int           // dynamic_offset_start
                                        "," Int           // i
                                                          // typ = top of keyz
                                                          // arg - top of CODE, which is a $multi()
                                        "," LLLExps       // subs - the result code
                                        ")"

    /* Other vars:
       variable_offset = LLLnode.from_list(['add', 32 * i, left_token], typ=arg.typ ...
          e.g.: variable_offset = $add(32 *Int i, $_loc)

       get_dynamic_offset_value() = $mload(DynOffsCouter)
    */

    // Case next type in tuple is BaseType:
    // subs.append(make_setter(variable_offset, arg, "memory", pos=getpos(self.stmt)))
    rule (. => #assignImpl(@tlll(ArgT, $add(32 *Int I, $_loc), @locattr(@memory, true)), Arg))
         ~> #returnTupleT(@tlll(%tupleT(ArgT:BaseType ArgTs => ArgTs), $multi(Arg ArgRest => ArgRest), _),
                          DynOffsCouter, NewSub, DynOffsetStart, I => I +Int 1, SUBS)

    /*  Case next type in tuple is ByteArrayType:

        subs.append(['mstore', variable_offset, get_dynamic_offset_value()])
        dynamic_spot = LLLnode.from_list(['add', left_token, get_dynamic_offset_value()], location="memory", ...
        subs.append(make_setter(dynamic_spot, arg, location="memory", pos=getpos(self.stmt)))
        subs.append(increment_dynamic_offset(dynamic_spot))

        def increment_dynamic_offset(dynamic_spot):
            return ['mstore', dynamic_offset_counter,
                                 ['add',
                                        ['add', ['ceil32', ['mload', dynamic_spot]], 32],
                                        ['mload', dynamic_offset_counter]]]
    */
    rule (. => #assignImpl(@tlll(ArgT, $add($_loc, $mload(DynOffsCouter))/*dynamic_spot*/, @locattr(@memory, true)), Arg)
               ~> #returnTupleByteArray(DynOffsCouter, I)
         )
         ~> #returnTupleT(@tlll(%tupleT(ArgT:ByteArrayType ArgTs => ArgTs), $multi(Arg ArgRest => ArgRest), _),
                          DynOffsCouter, NewSub, DynOffsetStart, I => I +Int 1, SUBS)

    syntax LLLExps ::= "#returnTupleByteArray" "(" Int "," Int ")"

    rule AssignResult:LLLExps ~> #returnTupleByteArray(DynOffsCouter, I)
         => ($mstore($add(32 *Int I, $_loc), $mload(DynOffsCouter)), .LLLExps)
            ++LLL AssignResult
            ++LLL $mstore(DynOffsCouter, $add($add($ceil32($mload($add($_loc, $mload(DynOffsCouter)))), 32),
                                              $mload(DynOffsCouter))),
                  .LLLExps

    rule (. => #exception("Can only return a tuple of base types or byte arrays!"))
         ~> #returnTupleT(@tlll(%tupleT(ArgT:Type _), _,_),
                          DynOffsCouter, NewSub, DynOffsetStart, I, SUBS)
      requires notBool (isBaseType(ArgT) orBool isByteArrayType(ArgT))

    rule (LocalResult:LLLExps => .)
         ~> #returnTupleT(_,_,_,_,_, SUBS => SUBS ++LLL LocalResult)

    /*  setter = LLLnode.from_list(['seq',
            ['mstore', dynamic_offset_counter, dynamic_offset_start],
            ['with', '_loc', new_sub, ['seq'] + subs]], typ=None
        )

        return LLLnode.from_list(['seq', setter, ['return', new_sub, get_dynamic_offset_value()]],
    */
    rule #returnTupleT(@tlll(%tupleT(.Types), _,_), DynOffsCouter, NewSub, DynOffsetStart, _, SUBS)
         => $%seq($mstore(DynOffsCouter, DynOffsetStart),
                  $with($_loc, NewSub, $%seq(SUBS)),
                  $return(NewSub, $mload(DynOffsCouter)), .LLLExps), .LLLExps

// Assert
// ======


    rule #compileStmt(%assert(EXPR)) => #assert(#compileToVal(EXPR))


    syntax CLLLExps  ::= "#assert" "(" CTypedLLLExp ")"  [strict]
 // -------------------------------------------------------------
    rule #assert(@tlll(_, CODE, _)) => $assert(CODE),.LLLExps


// Throw
// =====


    rule #compileStmt(%throw) => $assert(0),.LLLExps


// Log
// ====


    rule <k> #compileStmt(%log(NAME, ARGS)) => #log(ARGS, EVENTRECORD) ... </k>
         <internalSig>... NAME |-> EVENTRECORD:EventRecord ...</internalSig>

    rule <k> (. => #exception("Event not declared yet: " +String Id2String(NAME))) ~> #compileStmt(%log(NAME, _)) ...</k>
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
                                  ", actual: " +String Int2String(#numOfExprs(ARGS)))
                          ~> #log(ARGS, @event(EID, ENAME, EPARAMS)),
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

    syntax CPackedLoggingData  ::= "#packLoggingDataAux" "(" Exprs        "," // args - actual arguments
                                                             EventParams  "," // expected_data - formal params
                                                             LLLExps      "," // holder - output LLL code
                                                             CTypedLLLExp "," // dynamic_offset_counter
                                                             CTypedLLLExp "," // dynamic_placeholder
                                                             Int              // event params size
                                                         ")"    [seqstrict(4,5)]
    syntax CPackedLoggingData  ::= "#packLoggingDataAux2" "(" CPackedArgData ")"  [strict]
 // -------------------------------------------------------------------------
    rule #packLoggingData(ARGS, EPARAMS)
         => #packLoggingDataAux2(#packArguments(#compileExprs(ARGS), 0, #toParams(EPARAMS)))

    rule #packLoggingDataAux2(@argdata(CODE, ARGSSTART, ARGSWIDTH))
         => @loggingdata(CODE, ARGSSTART +Int 4, ARGSWIDTH -Int 4) //the substracted 4 are for function id

    syntax Params ::= "#toParams" "(" EventParams ")" [function]
 // -------------------------------------------------------------------------
    rule #toParams(%eparam(ID, T, false) EPS) => %param(ID, T) #toParams(EPS)
    rule #toParams(.EventParams) => .Params


    /*rule #packLoggingData(DARGS, EPARAMS)
        => #ifThenElse(#numOfExprs(DARGS) ==Int 0,
                       @loggingdata($pass, 0, 0),
                       #packLoggingDataAux(DARGS, EPARAMS, .LLLExps, #newPlaceholder(%num), #newPlaceholder(%num),
                                           #sizeOfEParams(EPARAMS)))*/

    rule #packLoggingDataAux(.Exprs, .EventParams, CODE, _, @tlll(_, DynPL:Int, _), STATICSize)
         => @loggingdata($%seq(CODE), DynPL +Int 32, STATICSize)

    //datamem_start = dynamic_placeholder + 32
    rule (. => #packArgBy32(#newPlaceholder(T), DARG, T, DynPL +Int 32, DynOC))
         ~> #packLoggingDataAux(DARG DARGS => DARGS, %eparam(_, T, _) DEPARAMS => DEPARAMS, HOLDER,
                                @tlll(_, DynOC:Int, _), @tlll(_, DynPL:Int, _), STATICSize)

    rule (@argby32(ARGCODE, ARGSIZE) => .)
         ~> #packLoggingDataAux(DARGS, DEPARAMS, HOLDER => HOLDER ++LLL ARGCODE, _,_,_)

    rule (ARGCODE:LLLExps => .)
         ~> #packLoggingDataAux(DARGS, DEPARAMS, HOLDER => HOLDER ++LLL ARGCODE, _,_,_)


    syntax CPackedArgBy32  ::= "#packArgBy32" "(" CTypedLLLExp ","  // placeholder
                                                  Expr         ","  // value
                                                  Type         ","  // expected type
                                                  Int          ","  // datamem_start
                                                  Int               // dynamic_offset_counter

                                              ")"      [strict(1)]
 // --------------------------------------------------------------
    // Base Type
    rule #packArgBy32(@tlll(_, LOC:Int, _), EXPR, T:BaseType, _,_)
        => #packArgBy32Base(LOC, #compileToLoc(EXPR), T)

    // String Literal
    rule #packArgBy32(@tlll(T, LOC:Int, LA), STR:String, %bytesT(L), Datamem, DynOC)
        => #ifThen(lengthString(STR) >Int L,
                   #exception("Data input bytes are too big.")
                      ~> #packArgBy32(@tlll(T, LOC:Int, LA), STR:String, %bytesT(L), Datamem, DynOC))
        ~> #packArgBy32StringLiteral(LOC, #string2Bytes(STR))

    // Byte Array Variable
    rule #packArgBy32(@tlll(_, LOC:Int, _), EXPR, %bytesT(L), Datamem, DynOC)
        => #pack_args_by_32_BytesT_Var(L, #compileToLoc(EXPR), %bytesT(L))
      requires notBool isString(EXPR)

    // Lists.
    rule #packArgBy32(@tlll(T:ListType, LOC:Int, LA), EXPR, T, Datamem, DynOC)
         => #assignImpl(@tlll(T, LOC:Int, LA), #compileToVal(EXPR))


    syntax CPackedArgBy32  ::= "#packArgBy32Base"    "(" Int          ","  // packing loc
                                                         CTypedLLLExp ","
                                                         Type              // arg type
                                                     ")"      [strict(2)]

    syntax CPackedArgBy32  ::= "#packArgBy32BaseAux" "(" Int          ","
                                                         CTypedLLLExp ")"  [strict(2)]
 // ----------------------------------------------------------------------------------
    rule #packArgBy32Base(LOC, TCODE, ARGTYPE)
        => #packArgBy32BaseAux(LOC, #baseTypeConvert(TCODE, ARGTYPE))

    rule #packArgBy32BaseAux(PLLoc, @tlll(_, CODE, _)) => @argby32($mstore(PLLoc, CODE),.LLLExps, 32)


    syntax CPackedArgBy32  ::= "#packArgBy32StringLiteral" "(" Int    ","  // packing loc
                                                               CBytes ")"  [strict(2)]
 // ----------------------------------------------------------------------------------
    rule #packArgBy32StringLiteral(LOC, BS)
        => @argby32($mstore(LOC, #bytes2Int(BS, 32, 0)), 32)


    syntax CPackedArgBy32  ::= "#pack_args_by_32_BytesT_Var" "(" Int          "," // placeholder
                                                                 CTypedLLLExp "," // value
                                                                 Type             // arg type
                                                             ")"      [strict(2)]
 // -----------------------------------------------------------------------



    syntax CPackedArgBy32  ::= "#packArgBy32ListTLiteral" "(" Int     ","  // packing loc
                                                              Exprs   ","
                                                              Type    ","  // arg type
                                                              LLLExps ","  // result code
                                                              Int     ")"  // total size
 // ---------------------------------------------------------------------
    rule #packArgBy32ListTLiteral(LOC, .Exprs, T, RESULTCODE, TOTALSIZE)
        => @argby32(RESULTCODE, TOTALSIZE)

    rule (. => #packArgBy32(@tlll(SUBTYPE, LOC, @locattr(@memory, true)), EXPR, SUBTYPE, 0,0)) //last 2 args unused
         ~> #packArgBy32ListTLiteral(LOC, EXPR EXPRS => EXPRS, %listT(SUBTYPE, N), RESULTCODE, TOTALSIZE)

    rule (@argby32(CODE, SIZE) => .)
         ~> #packArgBy32ListTLiteral(LOC => LOC +Int SIZE, EXPRS, T,
                                     RESULTCODE => RESULTCODE ++LLL CODE, TOTALSIZE => TOTALSIZE +Int SIZE)


    syntax CPackedArgBy32  ::= "#packArgBy32ListTVar" "(" Int          ","  // packing loc
                                                          CTypedLLLExp ","
                                                          Type         ","  // arg type
                                                          LLLExps      ","  // result code
                                                          Int          ","  // index
                                                          Int          ")"  // total size
 // ----------------------------------------------------------------------
    // TODO: https://github.com/ethereum/vyper/issues/551


    syntax CTypedLLLExp  ::= "#packLoggingTopic" "(" Expr "," EventParams ")"
 // -------------------------------------------------------------------------
    // Base Type
    rule #packLoggingTopic(ARG, %eparam(_, T, _)) => #packLoggingTopicBase(#compileToLoc(ARG), T:BaseType)

    // String Literal
    rule #packLoggingTopic(ARG:String, %eparam(ID, %bytesT(L), B))
         => #ifThenElse(lengthString(ARG) >Int L,
                        #exception("Topic input bytes are to big.")
                          ~> #packLoggingTopic(ARG:String, %eparam(ID, %bytesT(L), B)),
                        #packLoggingTopicStringLiteral(#string2Bytes(ARG), %bytesT(L)))

    // Byte Array Variable
    rule #packLoggingTopic(ARG, %eparam(_, %bytesT(L), _))
        => #packLoggingTopicBytesTVar(#compileToLoc(ARG), %bytesT(L))
      requires notBool isString(ARG)



    syntax CTypedLLLExp  ::= "#packLoggingTopicBase" "(" CTypedLLLExp "," Type ")"  [strict(1)]
 // -------------------------------------------------------------------------------------------
    rule #packLoggingTopicBase(ARGCODE, T) => #baseTypeConvert(ARGCODE, T)


    syntax CTypedLLLExp  ::= "#packLoggingTopicStringLiteral" "(" CBytes "," Type ")"  [strict(1)]
 // ----------------------------------------------------------------------------------------------
    rule #packLoggingTopicStringLiteral(BS, %bytesT(L)) => @tlll(%bytesT(L), #bytes2Int(BS, 32, 0), @none)


    syntax CTypedLLLExp  ::= "#packLoggingTopicBytesTVar" "(" CTypedLLLExp "," Type ")"  [strict(1)]
 // ------------------------------------------------------------------------------------------------
    rule #packLoggingTopicBytesTVar(@tlll(%bytesT(L), CODE, LA), _)
         => #byte_array_to_num(@tlll(%bytesT(L), CODE, LA), %num256, L) //not sure what's the last arg.


// Statement Expression
// ====================


    rule #compileStmt(%stmtexpr(EXPR)) => #stmtExpr(EXPR)


    syntax CLLLExps  ::= "#stmtExpr" "(" Expr ")"
 // ---------------------------------------------


    syntax CLLLExps  ::= "#icallNoReturn" "(" Exprs "," FuncRecord ")"
 // ----------------------------------------------------------------------
    rule <k> #stmtExpr(%icall(FNAME, EXPRS)) => #icallNoReturn(EXPRS, FUNCRECORD) ... </k>
         <internalSig>... FNAME |-> FUNCRECORD ...</internalSig>

    // TODO: Is it necessary to enforce that functions cannot call functions defined later than themselves?
    rule <k> (. => #exception("Function not declared yet: " +String Id2String(FNAME)))
             ~> #stmtExpr(%icall(FNAME, _)) ... </k>
         <internalSig> SIGS </internalSig>
      requires notBool FNAME in_keys(SIGS)

    // EVM: CALL GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
    rule #icallNoReturn(ARGS, @func(FUNCID, FNAME, PARAMS, RETT, B1, B2, B3))
         => #ifThenElse(#numOfExprs(ARGS) =/=K #numOfParams(PARAMS),
                        #exception("# of args doesn't match # of params in function" +String Id2String(FNAME) +String
                                " expected: " +String Int2String(#numOfParams(PARAMS)) +String
                                ", actual: " +String Int2String(#numOfExprs(ARGS)))
                          ~> #icallNoReturn(ARGS, @func(FUNCID, FNAME, PARAMS, RETT, B1, B2, B3)),
                        #icallNoReturnAux(#packArguments(#compileExprs(ARGS), FUNCID, PARAMS)))


    syntax CLLLExps  ::= "#icallNoReturnAux" "(" CPackedArgData ")"  [strict]
 // -------------------------------------------------------------------------
    rule #icallNoReturnAux(@argdata(CODE, _, ARGSWIDTH))
        => $assert($call($gas, $address, 0, CODE, ARGSWIDTH, 0, 0)),.LLLExps


// Send
// ====


    rule <k> #compileStmt(%send(TO, VALUE))
            => #ifThenElse(CONSTANT ==K true,
                           #exception("Cannot send ether inside a constant function") ~> #compileStmt(%send(TO, VALUE)),
                           #send(#compileToVal(TO), #compileToVal(VALUE))) ... </k>
         <constant> CONSTANT </constant>


    syntax CLLLExps  ::= "#send"    "(" CTypedLLLExp /*to*/ "," CTypedLLLExp /*value*/ ")"  [seqstrict]
    syntax CLLLExps  ::= "#sendAux" "(" TypedLLLExp "," TypedLLLExp ")"
 // ---------------------------------------------------------------------------------------------------
    rule #send(TTOCODE, @tlll(T, VALUECODE, EXPRATTR))
        => #sendAux(TTOCODE,
                    @tlll(#convertToUnitIfPure(T, @unittuple((%wei |-> 1), false)), VALUECODE, EXPRATTR))

    rule #sendAux(@tlll(_:AddressType, TOCODE, _), @tlll(%unitT(%num, %wei |-> 1, false), VALUECODE, _))
        => $assert($call(0, TOCODE, VALUECODE, 0, 0, 0, 0)),.LLLExps


// Selfdestruct
// ============


    rule <k> (. => #exception("Cannot self destruct inside a constant function! "))
             ~> #compileStmt(%selfdestruct(ADDR)) ...</k>
         <constant> true </constant>

    rule <k> #compileStmt(%selfdestruct(ADDR))
            => #selfdestruct(#compileToVal(ADDR))
         ... </k>
         <constant> false </constant>


    syntax CLLLExps  ::= "#selfdestruct" "(" CTypedLLLExp ")"  [strict]
 // -------------------------------------------------------------------
    rule #selfdestruct(@tlll(_:AddressType, ADDRCODE, _)) => $selfdestruct(ADDRCODE),.LLLExps



///////////////////////////////////////////////////////////////////////////////
// Expressions
///////////////////////////////////////////////////////////////////////////////


    syntax CTypedLLLExps  ::= "#compileExprs" "(" Exprs ")"
    syntax CTypedLLLExps  ::= "#compileExprsAux" "(" Exprs "," TypedLLLExps ")"
 // ---------------------------------------------------------------------------
    rule #compileExprs(EXPRS) => #compileExprsAux(EXPRS, .TypedLLLExps)

    rule #compileExprsAux(.Exprs, RESULTCODE) => RESULTCODE

    rule #compileExprsAux((EXPR EXPRS), RESULTCODE)
        => #compileToVal(EXPR)
        ~> #compileExprsAux(EXPRS, RESULTCODE)

    rule TCODE:TypedLLLExp ~> #compileExprsAux(EXPRS, RESULTCODE)
        => #compileExprsAux(EXPRS, RESULTCODE ++TLLL (TCODE .TypedLLLExps))


    // Compile an expression that results in a value
    syntax CTypedLLLExp  ::= "#compileToVal"    "(" Expr ")"
    syntax CTypedLLLExp  ::= "#compileToValAux" "(" CTypedLLLExp ")"  [strict]
 // ------------------------------------------------------------------------------
    rule #compileToVal(EXPR:Expr) => #compileToValAux(#compileToLoc(EXPR))

    rule #compileToValAux(TCODE) => #unwrapLoc(TCODE)


    // Compile an expression that represents an address in memory or storage
    syntax CTypedLLLExp  ::= "#compileLocExpr"    "(" Expr ")"
    syntax CTypedLLLExp  ::= "#compileLocExprAux" "(" CTypedLLLExp ")"  [strict]
 // ----------------------------------------------------------------------------
    rule #compileLocExpr(EXPR) => #compileLocExprAux(#compileToLoc(EXPR))

    rule #compileLocExprAux(@tlll(T, CODE, EXPRATTR))
        => #ifThenElse(EXPRATTR ==K @none,
                       #exception("Looking for a variable location, instead got a value")
                          ~> #compileLocExprAux(@tlll(T, CODE, EXPRATTR)),
                       @tlll(T, CODE, EXPRATTR))


    /*  Produces @none locations only for constants.
        Otherwise producs @memory/@storage lcoations, regardless of expression type.
    */
    syntax CTypedLLLExp  ::= "#compileToLoc" "(" Expr ")"
 // ----------------------------------------------------

// Number
// ======


    rule #compileToLoc(NUM:Int) => #ifThenElse((NUM >=Int @minNum) andBool (NUM <=Int @maxNum),
                                              @tlll(%num, NUM, @none),
                                              #exception("Number out of range") ~> #compileToLoc(NUM))

    rule #compileToLoc(%fixed10(NUM, DEN))
        => #ifThen(notBool((NUM >=Int (@minNum *Int DEN)) andBool (NUM >=Int (@minNum *Int DEN))),
                   #exception("Number out of range.") ~> #compileToLoc(%fixed10(NUM, DEN)))
        ~> #ifThen(@decimalDivisor <Int DEN,
                   #exception("Too many decimal places.") ~> #compileToLoc(%fixed10(NUM, DEN)))
        ~> @tlll(%decimal, (NUM *Int @decimalDivisor) /Int DEN, @none)

    rule #compileToLoc(%hex(STR))
        => #ifThenElse(lengthString(STR) ==Int 40,
                       @tlll(%address, String2Base(STR, 16), @none),
             #ifThenElse(lengthString(STR) ==Int 64,
                         @tlll(%bytes32, String2Base(STR, 16), @none),
                         #exception("Cannot read 0x value with length:" +String Int2String(lengthString(STR)))
                            ~> #compileToLoc(%hex(STR))))


// String Literal
// ===============


    rule #compileToLoc(STR:String) => #string(#string2Bytes(STR))


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


    rule #compileToLoc(true)  => @tlll(%bool, 1, @none)

    rule #compileToLoc(false)  => @tlll(%bool, 0, @none)

// None Literal
// ===============
    rule #compileToLoc(%None)  => @tlll(%NoneType, 0, @none)

    syntax Type ::= "%NoneType"

    rule #assign(V, @tlll(%NoneType, _, _))
         => #assignNone(#getTarget(V, #lookupVar(V)))

    // Assign None expression: V = None.
    // Semantics: Writes zero over entire memory space of the LHS variable.
    syntax CLLLExps  ::= "#assignNone" "(" CTypedLLLExp  /*left variable loc*/  ")"  [seqstrict]
 // -----------------------------------------------------------------

    rule #assignNone(@tlll(T:Type, LOC:LLLExp, @locattr(@memory, _)))
         => $with($_opos, LOC,
                $repeat(@freeLoopIndexPos, 0, #sizeOfType(T) /Int 32,
                        $mstore($add($_opos, $mul(32, $mload(@freeLoopIndexPos))),
                                0))),.LLLExps

    //WARN: Storage nullification will only work for first level of composite data types.
    //Are None assignments allowed for multi-level composites? Like:  a:num[2][2] a=None
    rule #assignNone(@tlll(T:Type, LOC:LLLExp, @locattr(@storage, _)))
         => $with($_opos, $sha3_32(LOC),
                $repeat(@freeLoopIndexPos, 0, #sizeOfType(T) /Int 32,
                        $sstore($add($_opos, $mload(@freeLoopIndexPos)),
                                0))),.LLLExps


// Variable
// ========


    rule #compileToLoc(%self) => @tlll(%address, $address, @none)

    rule #compileToLoc(V:Var) => #lookupVar(V)


// List Literal
// =============


    rule #compileToLoc(%list(EXPRS)) => #listLiteral(EXPRS)
      requires #numOfExprs(EXPRS) >Int 0

    rule (. => #exception("List must have elements")) ~> #compileToLoc(%list(.Exprs))


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
    rule #processListLiteralFirstElem(EXPR) => #compileToLoc(EXPR)


    syntax CTypedLLLExp  ::= "#processListLiteralRestElems"    "(" Exprs "," TypedLLLExps ")"
    syntax CTypedLLLExp  ::= "#processListLiteralRestElemsAux" "(" Type "," Int "," Exprs "," TypedLLLExps ")"
 // -----------------------------------------------------------------------------------------------------------
    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralRestElems(EXPRS, .TypedLLLExps)
        => #processListLiteralRestElemsAux(T, 1, EXPRS, @tlll(T, CODE, EXPRATTR) .TypedLLLExps)

    rule #processListLiteralRestElemsAux(T, LEN, .Exprs, RESULTCODE)
        => @tlll(%listT(T, LEN), $multi(RESULTCODE), @none)

    rule #processListLiteralRestElemsAux(T, LEN, (EXPR EXPRS), RESULTCODE)
        => #compileToLoc(EXPR) ~> #processListLiteralRestElemsAux(T, LEN, EXPRS, RESULTCODE)

    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralRestElemsAux(T, LEN, EXPRS, RESULTCODE)
        => #processListLiteralRestElemsAux(T, LEN +Int 1, EXPRS,
                                           RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))

    rule @tlll(T, CODE, EXPRATTR) ~> #processListLiteralRestElemsAux(ELEMT, LEN, EXPRS, RESULTCODE)
        => #processListLiteralRestElemsAux(%mixedT, LEN +Int 1, EXPRS,
                                           RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))
      requires T =/=K ELEMT


// Struct Literal
// ===============


    rule #compileToLoc(%struct(ITEMS)) => #structLiteral(ITEMS, .Ids, .AnnVars, .TypedLLLExps)


    syntax CTypedLLLExp  ::= "#structLiteral" "(" StructItems  ","
                                                  Ids          ","  // names of the fields (for name duplication check)
                                                  AnnVars      ","  // struct fields (for inferring struct type)
                                                  TypedLLLExps ")"  // result code

    syntax KItem  ::= "#nameWithValue" "(" Id "," CTypedLLLExp ")"    [strict(2)]
 // -----------------------------------------------------------------------------
    rule #structLiteral(%item(NAME, EXPR) ITEMS, NAMES, ANNVARS, RESULTCODE)
        => #ifThen(notBool #isVarNameValid(NAME),
                   #exception("Invalid member variable for struct.")
                      ~> #structLiteral(%item(NAME, EXPR) ITEMS, NAMES, ANNVARS, RESULTCODE))
        ~> #ifThen(#inIds(NAME, NAMES),
                   #exception("Member variable duplicated: " +String Id2String(NAME))
                      ~> #structLiteral(%item(NAME, EXPR) ITEMS, NAMES, ANNVARS, RESULTCODE))
        ~> #nameWithValue(NAME, #compileToLoc(EXPR))
        ~> #structLiteral(ITEMS, NAMES, ANNVARS, RESULTCODE)

    rule (#nameWithValue(NAME, @tlll(T, CODE, EXPRATTR)) => .)
        ~> #structLiteral(_,
                          NAMES => NAMES ++Id (NAME .Ids),
                          ANNVARS => ANNVARS ++Annvar (%annvar(NAME, T) .AnnVars),
                          RESULTCODE => RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))

    rule #structLiteral(.StructItems, NAMES, ANNVARS, RESULTCODE)
        => @tlll(%structT(ANNVARS), $multi(RESULTCODE), @none)


// Tuple Literal
// ===============

    rule #compileToLoc(%tuple(Ts)) => #tupleLiteral(Ts, .Types, .TypedLLLExps)


    syntax CTypedLLLExp  ::= "#tupleLiteral"  "(" Exprs        ","  // elements
                                                  Types        ","  // elements type (for inferring struct type)
                                                  TypedLLLExps      // result code
                                              ")"
 // -----------------------------------------------------------------------------
    rule (. => #compileToLoc(E)) ~> #tupleLiteral(E Es => Es, Ts, RESULTCODE)

    rule (@tlll(T, CODE, EXPRATTR) => .)
         ~> #tupleLiteral(_,
                          Ts => Ts ++Types T .Types,
                          RESULTCODE => RESULTCODE ++TLLL (@tlll(T, CODE, EXPRATTR) .TypedLLLExps))

    rule #tupleLiteral(.Exprs, Ts, RESULTCODE)
         => @tlll(%tupleT(Ts), $multi(RESULTCODE), @none)


// Arithmetic
// ==========


    rule #compileToLoc(%binop(BOP, LEXPR, REXPR))
        => #binOp(BOP, #compileToVal(LEXPR), #compileToVal(REXPR))


    syntax CTypedLLLExp  ::= "#binOp" "(" BinOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
 // ---------------------------------------------------------------------------------------------------
    rule #binOp(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
                   #exception("Unsupported types for arithmetic op")
                      ~> #binOp(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR)))
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
    rule #newUnitTuple(+, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE)
        => #ifThen(LM =/=K RM,
                   #exception("Unit mismatch.")
                      ~> #newUnitTuple(+, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE))
        ~> #ifThen(LPOS ==K true andBool RPOS ==K true,
                   #exception("Cannot add two positional units!")
                      ~> #newUnitTuple(+, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE))
        ~> @unittuple(LM, LPOS xorBool RPOS)

    rule #newUnitTuple(+, %unitT(LT, LM:Map, LPOS), RT:PureNumType, _)
        => @unittuple(LM, LPOS)

    rule #newUnitTuple(+, LT:PureNumType, %unitT(RT, RM:Map, RPOS), _)
        => @unittuple(RM, RPOS)

    // subtract
    rule #newUnitTuple(-, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE)
        => #ifThen(LM =/=K RM,
                   #exception("Unit mismatch.")
                      ~> #newUnitTuple(-, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE))
        ~> @unittuple(LM, LPOS xorBool RPOS)

    rule #newUnitTuple(-, %unitT(LT, LM:Map, LPOS), RT:PureNumType, _)
        => @unittuple(LM, LPOS)

    rule #newUnitTuple(-, LT:PureNumType, %unitT(RT, RM:Map, RPOS), _)
        => @unittuple(RM, RPOS)

    // multiply
    rule #newUnitTuple(*, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE)
        => #ifThen(LPOS ==K true orBool RPOS ==K true,
                   #exception("Cannot multiply positional values!")
                      ~> #newUnitTuple(*, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE))
        ~> @unittuple(#combineUnits(LM, RM, false), false)

    rule #newUnitTuple(*, %unitT(LT, LM:Map, LPOS), RT:PureNumType, LLLE)
        => #ifThen(LPOS ==K true,
                   #exception("Cannot multiply positional values!")
                      ~> #newUnitTuple(*, %unitT(LT, LM:Map, LPOS), RT:PureNumType, LLLE))
        ~> @unittuple(LM, false)

    rule #newUnitTuple(*, LT:PureNumType, %unitT(RT, RM:Map, RPOS), LLLE)
        => #ifThen(RPOS ==K true,
                   #exception("Cannot multiply positional values!")
                      ~> #newUnitTuple(*, LT:PureNumType, %unitT(RT, RM:Map, RPOS), LLLE))
        ~> @unittuple(RM, false)

    // divide
    rule #newUnitTuple(/, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE)
        => #ifThen(LPOS ==K true orBool RPOS ==K true,
                   #exception("Cannot divide positional values!")
                      ~> #newUnitTuple(/, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE))
        ~> @unittuple(#combineUnits(LM, RM, true), false)

    rule #newUnitTuple(/, %unitT(LT, LM:Map, LPOS), RT:PureNumType, LLLE)
        => #ifThen(LPOS ==K true,
                   #exception("Cannot divide positional values!")
                      ~> #newUnitTuple(/, %unitT(LT, LM:Map, LPOS), RT:PureNumType, LLLE))
        ~> @unittuple(LM, false)

    rule #newUnitTuple(/, LT:PureNumType, %unitT(RT, RM:Map, RPOS), LLLE)
        => #ifThen(RPOS ==K true,
                   #exception("Cannot divide positional values!")
                      ~> #newUnitTuple(/, LT:PureNumType, %unitT(RT, RM:Map, RPOS), LLLE))
        ~> @unittuple(#combineUnits(.Map, RM, true), false)

    // mod
    rule #newUnitTuple(%, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE)
        => #ifThen(LPOS ==K true orBool RPOS ==K true,
                   #exception("Cannot use positional values as modulus arguments!")
                      ~> #newUnitTuple(%, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE))
        ~> #ifThen(LM =/=K RM,
                   #exception("Modulus arguments must have same unit.")
                      ~> #newUnitTuple(%, %unitT(T1, LM:Map, LPOS), %unitT(T2, RM:Map, RPOS), LLLE))
        ~> @unittuple(LM, false)

    rule #newUnitTuple(%, %unitT(LT, LM:Map, LPOS), RT:PureNumType, LLLE)
        => #ifThen(LPOS ==K true,
                   #exception("Cannot use positional values as modulus arguments!")
                      ~> #newUnitTuple(%, %unitT(LT, LM:Map, LPOS), RT:PureNumType, LLLE))
        ~> @unittuple(LM, false)

    rule #newUnitTuple(%, LT:PureNumType, %unitT(RT, RM:Map, RPOS), LLLE)
        => #ifThen(RPOS ==K true,
                   #exception("Cannot use positional values as modulus arguments!")
                      ~> #newUnitTuple(%, LT:PureNumType, %unitT(RT, RM:Map, RPOS), LLLE))
        ~> @unittuple(RM, false)

    // exp
    rule (. => #exception("Cannot use unit values as exponents"))
         ~> #newUnitTuple(**, _, %unitT(_, RM:Map, RPOS), _)

    rule #newUnitTuple(**, %unitT(LT, LM:Map, LPOS), %num, POW:Int)
        => @unittuple(#computeUnitPow(LM, POW), false)

    rule (. => #exception("Only whole number exponents are supported"))
         ~> #newUnitTuple(**, %unitT(LT, LM:Map, LPOS), RT:PureNumType, CODE)
      requires notBool isInt(CODE)


    syntax CTypedLLLExp  ::= "#binOpPure"    "(" BinOp "," TypedLLLExp "," TypedLLLExp ")"
    syntax CTypedLLLExp  ::= "#binOpPureAux" "(" BinOp "," TypedLLLExp "," TypedLLLExp ")"
 // --------------------------------------------------------------------------------------
    rule #binOpPure(BOP, LTCODE, RTCODE)
        => #binOpPureAux(BOP, LTCODE, RTCODE)
        ~> #clampArithResult

    rule #binOpPureAux(+, @tlll(LT, LCODE, @none), @tlll(RT, RCODE, @none))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $add(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                         @tlll(%decimal, $add($mul(LCODE, @decimalDivisor), RCODE), @none),
               #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                           @tlll(%decimal, $add(LCODE, $mul(RCODE, @decimalDivisor)), @none),
                           #exception("How did I get here?")
                              ~> #binOpPureAux(+, @tlll(LT, LCODE, @none), @tlll(RT, RCODE, @none)))))

    rule #binOpPureAux(-, @tlll(LT, LCODE, @none), @tlll(RT, RCODE, @none))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $sub(LCODE, RCODE), @none),
             #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                         @tlll(%decimal, $sub($mul(LCODE, @decimalDivisor), RCODE), @none),
               #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                           @tlll(%decimal, $sub(LCODE, $mul(RCODE, @decimalDivisor)), @none),
                           #exception("How did I get here?")
                              ~> #binOpPureAux(-, @tlll(LT, LCODE, @none), @tlll(RT, RCODE, @none)))))

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
        => #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                       @tlll(%decimal, $sdiv(LCODE, $clamp_nonzero(RCODE)), @none),
              #ifThenElse(LT ==K %num andBool RT ==K %num,
                          @tlll(%decimal, $sdiv($mul(LCODE, @decimalDivisor), $clamp_nonzero(RCODE)), @none),
                #ifThenElse(LT ==K %decimal andBool RT ==K %decimal,
                         @tlll(%decimal, $with($l, LCODE,
                                           $with($r, $clamp_nonzero(RCODE),
                                             $sdiv($mul($l, @decimalDivisor), $r))), @none),
                  #ifThen(LT ==K %num andBool RT ==K %decimal,
                          @tlll(%decimal,
                             $sdiv($mul(LCODE, @decimalDivisor ^Int 2), $clamp_nonzero(RCODE)), @none)))))

    rule #binOpPureAux(%, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => #ifThenElse(LT ==K RT,
                       @tlll(LT, $smod(LCODE, $clamp_nonzero(RCODE)), @none),
             #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                         @tlll(%decimal, $smod(LCODE, $mul($clamp_nonzero(RCODE), @decimalDivisor)), @none),
               #ifThen(LT ==K %num andBool RT ==K %decimal,
                       @tlll(%decimal, $smod($mul(LCODE, @decimalDivisor), $clamp_nonzero(RCODE)), @none))))

    rule #binOpPureAux(**, @tlll(LT, LCODE, @none), @tlll(RT, RCODE, @none))
        => #ifThenElse(LT ==K %num andBool RT ==K %num,
                       @tlll(%num, $exp(LCODE, RCODE), @none),
                       #exception("Only whole number exponents are supported")
                          ~> #binOpPureAux(**, @tlll(LT, LCODE, @none), @tlll(RT, RCODE, @none)))


    syntax KItem  ::= "#clampArithResult"
 // -------------------------------------
    rule @tlll(%num, CODE, _) ~> #clampArithResult
        => @tlll(%num, $clamp($mload(@minNumPos), CODE, $mload(@maxNumPos)), @none)

    rule @tlll(%decimal, CODE, _) ~> #clampArithResult
        => @tlll(%decimal, $clamp($mload(@minDecimalPos), CODE, $mload(@maxDecimalPos)), @none)


// Compare
// =======

    rule #compileToLoc(%compareop(COP, LEXP, REXP))
        => #compareOp(COP, #compileToVal(LEXP), #compileToVal(REXP))
    requires COP =/=K %in

    rule #compileToLoc(%compareop(%in, LEXP, REXP))
        => #inOperatorAux(LEXP, REXP, #compileToLoc(LEXP), #compileToLoc(REXP), #newVarId, #newVarId)


// Compare - in operator
// ---------------------
    syntax CTypedLLLExp  ::= "#inOperatorAux" "(" Expr          "," // LHS
                                                  Expr          "," // RHS
                                                  CTypedLLLExp  "," // LHS compiled
                                                  CTypedLLLExp  "," // RHS compiled
                                                  K             "," // aux var - result
                                                  K                 // aux var - loop iterator
                                              ")"               [seqstrict(3,4,5,6)]

    /* Desugaring template:
        a %in list
    =>
        rez = False
        for i %in list:
            if a == i: rez = True
        rez;
    */
    // TODO: https://github.com/ethereum/vyper/issues/581
    //       https://github.com/ethereum/vyper/issues/582
    //       Need to think carefully how to implement list and type casting.
    rule #inOperatorAux(LEXP, REXP,
                        @tlll(LT, LCODE, _), @tlll(%listT(LElemType:Type, _), RCODE, _),
                        RESULTID:Id, LOOPID:Id)
        => #ifThen(notBool(#areUnitsCompatible(LT, LElemType, #isNumLiteral(LCODE))) andBool
                   notBool(#areUnitsCompatible(LElemType, LT, #isNumLiteral(RCODE))),
                   #exception("Can't use IN comparison with different types!"))
        ~> #exprSeq(
              #compileStmts((
                %assign(%var(RESULTID), false)
                %forlist(LOOPID, REXP,
                         %if(%compareop(%eq, LEXP, %var(LOOPID)),
                             %assign(%var(RESULTID), true)))),
                .LLLExps),
              #compileToVal(%var(RESULTID))
           )


// Compare - operators other than "in"
// ---------------------
    syntax CTypedLLLExp  ::= "#compareOp" "(" CompareOp    ","
                                              CTypedLLLExp ","
                                              CTypedLLLExp
                                          ")"  [seqstrict(2,3)]
 // -----------------------------------------------------------
    rule #compareOp(COP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(notBool(#areUnitsCompatible(LT, RT, #isNumLiteral(LCODE))) andBool
                   notBool(#areUnitsCompatible(RT, LT, #isNumLiteral(RCODE))),
                   #exception("Can't compare values with different units!")
                      ~> #compareOp(COP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR)))
        ~> #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
             #ifThen(COP =/=K %eq andBool COP =/=K %ne,
                     #exception("Invalid type for comparison op")
                        ~> #compareOp(COP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))))
        ~> #compareOpAux(COP,
                         @tlll(#dropUnit(LT), LCODE, LEXPRATTR),
                         @tlll(#dropUnit(RT), RCODE, REXPRATTR))


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


    rule #compileToLoc(%boolop(BOP, LEXP, REXP)) => #boolOp(BOP, #compileToVal(LEXP), #compileToLoc(REXP))


    syntax CTypedLLLExp  ::= "#boolOp" "(" BoolOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp  ::= "#boolOpAux" "(" BoolOp "," TypedLLLExp "," TypedLLLExp ")"
 // ----------------------------------------------------------------------------------------------------
    rule #boolOp(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThenElse((LT ==K %bool) andBool (RT ==K %bool),
                        #boolOpAux(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR)),
                        #exception("Boolean operations can only be between booleans!")
                          ~> #boolOp(BOP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR)))

    rule #boolOpAux(%and, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => @tlll(%bool, $and(LCODE, RCODE), @none)

    rule #boolOpAux(%or, @tlll(LT, LCODE, _), @tlll(RT, RCODE, _))
        => @tlll(%bool, $or(LCODE, RCODE), @none)


// Unary Operation
// ===============


    rule #compileToLoc(%unaryop(UOP, EXPR)) => #unaryOp(UOP, #compileToVal(EXPR))


    syntax CTypedLLLExp  ::= "#unaryOp" "(" UnaryOp "," CTypedLLLExp ")"    [strict(2)]
 // -----------------------------------------------------------------------------------
    rule #unaryOp(%not, @tlll(T, CODE, _)) => @tlll(%bool, $iszero(CODE), @none)

    rule #unaryOp(%neg, @tlll(T:NumericType, CODE, _)) => @tlll(T, $sub(0, CODE), @none)

    rule (. => #exception("Unsupported type for negation."))
         ~> #unaryOp(%neg, @tlll(T, CODE, _))
      requires notBool isNumericType(T)



// Internal Contract Call
// ======================


    syntax CTypedLLLExp  ::= "#icallWithReturn" "(" Exprs "," FuncRecord ")"
 // ------------------------------------------------------------------------
    rule <k> #compileToLoc(%icall(FNAME, ARGS)) => #icallWithReturn(ARGS, FUNCRECORD) ... </k>
         <internalSig>... FNAME |-> FUNCRECORD ...</internalSig>

    // TODO: Is it necessary to enforce that functions cannot call functions defined later than themselves?
    rule <k> (. => #exception("Function not declared yet: " +String Id2String(FNAME)))
             ~> #compileToLoc(%icall(FNAME, _)) ... </k>
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
    rule #icallWithReturnAux(PACKEDARGS, @tlll(RETT:BaseType, LOC, LOCATTR), RETWIDTH)
        => #icallWithReturner(PACKEDARGS, @tlll(RETT, LOC, LOCATTR), RETWIDTH, LOC)

    // Byte Array
    rule #icallWithReturnAux(PACKEDARGS, @tlll(RETT:ByteArrayType, LOC, LOCATTR), RETWIDTH)
        => #icallWithReturner(PACKEDARGS, @tlll(RETT, LOC, LOCATTR), RETWIDTH, LOC +Int 32)


    // TODO: List?


    syntax CTypedLLLExp  ::= "#icallWithReturner" "(" PackedArgData ","  // packed args
                                                      TypedLLLExp   ","  // return start
                                                      Int           ","  // return width
                                                      Int           ")"  // returner
 // -------------------------------------------------------------------
    rule #icallWithReturner(@argdata(CODE, _, ARGSWIDTH), @tlll(RETT, LOC, LOCATTR), RETWIDTH, RETURNER)
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
                             LOC +Int 28, #sizeOfPackedArgs(TARGS) +Int 4, 0, false)


    syntax CPackedArgData  ::= "#packArgumentsAux" "(" Int          ","  // packing loc for the first arg
                                                                         // placeholder + staticarray_offset + 32 + i * 32
                                                       TypedLLLExps ","  // typed args code
                                                       Params       ","  // params
                                                       Int          ","  // num of args
                                                       LLLExps      ","  // setter code
                                                       Int          ","  // start of the arg block (including the funcid): placeholder +28
                                                       Int          ","  // packed args width
                                                       Int          ","  // staticarray_offset
                                                       Bool              // need pos?
                                                   ")"
 // -------------------------------------------------------------------
    rule #packArgumentsAux(_, .TypedLLLExps, .Params, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, SARRO, false)
        => @argdata($%seq(SETTER ++LLL (ARGSSTART,.LLLExps)), ARGSSTART, ARGSWIDTH)

    rule #packArgumentsAux(_, .TypedLLLExps, .Params, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, SARRO, true)
        => @argdata($with($_poz, ARGNUM *Int 32 +Int SARRO,
                      $%seq(SETTER ++LLL (ARGSSTART,.LLLExps))), ARGSSTART, ARGSWIDTH)

    // Base Type
    // setters.append(make_setter(LLLnode.from_list(placeholder + staticarray_offset + 32 + i * 32, typ=typ), arg, 'memory'))
    rule #packArgumentsAux(ARGLOC, (TARG TARGS), (%param(_, T:BaseType) PARAMS),
                           ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, SARRO, NEEDPOS)
        => #assignImpl(@tlll(T, ARGLOC +Int SARRO, @locattr(@memory, true)), TARG)
        ~> #packArgumentsAux(ARGLOC, TARGS, PARAMS, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, SARRO, NEEDPOS)

    // Byte Array Type
    // fixme: Byte Array packing does not comply with ABI specification?
    // ABI says for byte arrays: enc(X) = enc(k) pad_right(X)
    // in reality it is encoded as enc(k) X, without padding to a chunk of 32 bytes.
    rule #packArgumentsAux(ARGLOC, (TARG TARGS), (%param(_, T:ByteArrayType) PARAMS),
                           ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, SARRO, NEEDPOS)
        => #packArgumentBytesT(@tlll(T, ARGLOC, @locattr(@memory, true)), TARG, ARGSSTART +Int 4, SARRO)
        ~> #packArgumentsAux(ARGLOC, TARGS, PARAMS, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, SARRO, true)

    // List Type
    /*  target = LLLnode.from_list([placeholder + 32 + staticarray_offset + i * 32], typ=typ, location='memory')
        setters.append(make_setter(target, arg, 'memory'))
        staticarray_offset += 32 * (typ.count - 1) //typ is Param type, taken from signature.
    */
    rule #packArgumentsAux(ARGLOC, (TARG TARGS), (%param(_, T:ListType) PARAMS),
                           ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, SARRO, NEEDPOS)
        => #ifThen(notBool isListType(#getType(TARG)),
                   #exception("Arg expects list type but actual type is not."))
        ~> #assignImpl(@tlll(T, ARGLOC +Int SARRO, @locattr(@memory, true)), TARG)
        ~> #packArgumentsAux(
                             ARGLOC,
                             TARGS, PARAMS, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH,
                             SARRO +Int (32 *Int (#getListTCount(T) -Int 1)), NEEDPOS)


    rule CODE:LLLExps ~> #packArgumentsAux(ARGLOC, TARGS, PARAMS, ARGNUM, SETTER, ARGSSTART, ARGSWIDTH, SARRO, NEEDPOS)
        => #packArgumentsAux(ARGLOC +Int 32, TARGS, PARAMS, ARGNUM, SETTER ++LLL CODE, ARGSSTART, ARGSWIDTH, SARRO, NEEDPOS)


    syntax CLLLExps  ::= "#packArgumentBytesT" "(" TypedLLLExp  ","  // typed arg loc
                                                   TypedLLLExp  ","  // typed arg value
                                                   Int          ","  // start of the arg block (excluding the func id)
                                                   Int               // staticarray_offset
                                               ")"

    syntax CLLLExps  ::= "#packArgumentBytesTAux" "(" TypedLLLExp ","  // arg copy
                                                      TypedLLLExp ","  // target
                                                      LLLExps     ","  // setter
                                                      LLLExp      ")"  // arg code
 // ---------------------------------------------------------------
    rule #packArgumentBytesT(@tlll(PARAMT, LOC, LOCATTR), @tlll(ARGT, ARGCODE, EXPRATTR), ARGBLOCKSTART, SARRO)
        => #ifThen(notBool isByteArrayType(ARGT),
                   #exception("Arg expects byte array type but actual type is not."))
        ~> #packArgumentBytesTAux(@tlll(ARGT, $_s, EXPRATTR),
                                  @tlll(PARAMT, $add(ARGBLOCKSTART, $_poz), @locattr(@memory, true)),
                                  ($mstore(LOC +Int SARRO, $_poz),.LLLExps),
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


// External Contract Call - typed addresses
// ======================

    //converting call over typed address to call over explicit contract
    rule #compileToLoc(%ecall(V:Var, FNAME:Id, Es:Exprs)) => #compileEcall(#compileToLoc(V), V, FNAME, Es)

    syntax CTypedLLLExp ::= "#compileEcall" "(" CTypedLLLExp
                                            "," Expr
                                            "," Id
                                            "," Exprs
                                            ")"   [strict(1)]

    rule #compileEcall(@tlll(%contractT(CONTR:Id), _,_), ADDRE:Expr, FNAME:Id, Es:Exprs)
         => #compileToLoc(%ecall(CONTR, ADDRE, FNAME, Es))


    rule #stmtExpr(%ecall(V:Var, FNAME:Id, Es:Exprs)) => #compileEcallStmt(#compileToLoc(V), V, FNAME, Es)

    syntax CTypedLLLExp ::= "#compileEcallStmt" "(" CTypedLLLExp
                                                "," Expr
                                                "," Id
                                                "," Exprs
                                                ")"   [strict(1)]

    rule #compileEcallStmt(@tlll(%contractT(CONTR:Id), _,_), ADDRE:Expr, FNAME:Id, Es:Exprs)
         => #stmtExpr(%ecall(CONTR, ADDRE, FNAME, Es))


// External Contract Call - expression
//  reference: def external_contract_call_expr()
// ======================

    rule <k> (. => #exception("Contract not declared yet: " +String Id2String(CONTR)))
             ~> #compileToLoc(%ecall(CONTR:Id, ADDRE:Expr, FNAME:Id, PARAMS:Exprs)) ...</k>
         <contracts> CONTRACTS </contracts>
      requires notBool CONTR in keys(CONTRACTS)

    rule <k> (. => #exception("Function not declared yet: " +String Id2String(FNAME)
                              +String "(reminder: function must be declared in the correct contract)"))
             ~> #compileToLoc(%ecall(CONTR:Id, ADDRE:Expr, FNAME:Id, PARAMS:Exprs)) ...</k>
         <contracts>... CONTR |-> FUNCS ...</contracts>
      requires notBool FNAME in keys(FUNCS)

    /*  inargs, inargsize = pack_arguments(sig, [parse_expr(arg, context) for arg in expr.args], context)
        output_placeholder = context.new_placeholder(typ=sig.output_type)
        if isinstance(sig.output_type, BaseType):
            returner = output_placeholder
        elif isinstance(sig.output_type, ByteArrayType):
            returner = output_placeholder + 32
        else:
            raise TypeMismatchException("Invalid output type: %r" % sig.output_type, expr)
    */
    rule <k> #compileToLoc(%ecall(CONTR:Id, ADDRE:Expr, FNAME:Id, ARGS:Exprs))
             => #ifThen(notBool(isBaseType(RETT) orBool isByteArrayType(RETT)),
                        #exception("Invalid output type"))
                ~> #ecallExpr(#packArguments(#compileExprs(ARGS), FUNCID, PARAMS),
                              #newPlaceholder(RETT), #compileToVal(ADDRE), RETT)
         ...</k>
         <contracts>... CONTR |-> ((FNAME |-> @func(FUNCID:Int, _, PARAMS:Params, RETT:Type, _,_,_)) _) ...</contracts>

    /*  sub = ['seq', ['assert', ['extcodesize', contract_address]],
                        ['assert', ['ne', 'address', contract_address]]]
        if context.is_constant:
            sub.append(['assert', ['staticcall', 'gas', contract_address, inargs, inargsize,
                        output_placeholder, get_size_of_type(sig.output_type) * 32]])
        else:
            sub.append(['assert', ['call', 'gas', contract_address, 0, inargs, inargsize,
                output_placeholder, get_size_of_type(sig.output_type) * 32]])
        sub.extend([0, returner])
        o = LLLnode.from_list(sub, typ=sig.output_type, location='memory', pos=getpos(expr))
    */
    syntax CTypedLLLExp ::= "#ecallExpr" "(" CPackedArgData //result of #packArguments() : inargs, inargsize
                                         "," CTypedLLLExp   //output_placeholder
                                         "," CTypedLLLExp   //address
                                         "," Type           //return type
                                         ")"    [seqstrict]

    rule <k> #ecallExpr(@argdata(CODE, _, SIZE), @tlll(_, PLACEHOLDERLoc:Int, _), @tlll(_, ADDR, @none), RETT:Type)
             => @tlll(RETT,
                      $%seq($assert($extcodesize(ADDR)),
                            $assert($ne($address, ADDR)),
                            $assert($staticcall($gas, ADDR, CODE, SIZE, PLACEHOLDERLoc, #sizeOfType(RETT))),

                            //sub.extend([0, returner])
                            0, #ifLLLExp(isBaseType(RETT), PLACEHOLDERLoc, PLACEHOLDERLoc +Int 32), .LLLExps
                      ),
                      @locattr(@memory, false))
         ...</k>
         <constant> true </constant>

    rule <k> #ecallExpr(@argdata(CODE, _, SIZE), @tlll(_, PLACEHOLDERLoc:Int, _), @tlll(_, ADDR, @none), RETT:Type)
             => @tlll(RETT,
                      $%seq($assert($extcodesize(ADDR)),
                            $assert($ne($address, ADDR)),
                            $assert($call($gas, ADDR, 0, CODE, SIZE, PLACEHOLDERLoc, #sizeOfType(RETT))),

                            //sub.extend([0, returner])
                            0, #ifLLLExp(isBaseType(RETT), PLACEHOLDERLoc, PLACEHOLDERLoc +Int 32), .LLLExps
                      ),
                      @locattr(@memory, false))
         ...</k>
         <constant> false </constant>


// External Contract Call - expression statement
//  reference: external_contract_call_stmt()
// ======================

    rule <k> (. => #exception("Contract not declared yet: " +String Id2String(CONTR)))
             ~> #stmtExpr(%ecall(CONTR:Id, ADDRE:Expr, FNAME:Id, PARAMS:Exprs)) ...</k>
         <contracts> CONTRACTS </contracts>
      requires notBool CONTR in keys(CONTRACTS)

    rule <k> (. => #exception("Function not declared yet: " +String Id2String(FNAME)
                              +String "(reminder: function must be declared in the correct contract)"))
             ~> #stmtExpr(%ecall(CONTR:Id, ADDRE:Expr, FNAME:Id, PARAMS:Exprs)) ...</k>
         <contracts>... CONTR |-> FUNCS ...</contracts>
      requires notBool FNAME in keys(FUNCS)

    rule <k> #stmtExpr(%ecall(CONTR:Id, ADDRE:Expr, FNAME:Id, ARGS:Exprs))
             => #ecallStmt(#packArguments(#compileExprs(ARGS), FUNCID, PARAMS), #compileToVal(ADDRE))
         ...</k>
         <contracts>... CONTR |-> ((FNAME |-> @func(FUNCID:Int, _, PARAMS:Params, _,_,_,_)) _) ...</contracts>

    /*  inargs, inargsize = pack_arguments(sig, [parse_expr(arg, context) for arg in stmt.args], context)
        sub = ['seq', ['assert', ['extcodesize', contract_address]],
                        ['assert', ['ne', 'address', contract_address]]]
        if context.is_constant:
            sub.append(['assert', ['staticcall', 'gas', contract_address, inargs, inargsize, 0, 0]])
        else:
            sub.append(['assert', ['call', 'gas', contract_address, 0, inargs, inargsize, 0, 0]])
        o = LLLnode.from_list(sub, typ=sig.output_type, location='memory', pos=getpos(stmt))
    */
    syntax CLLLExps ::= "#ecallStmt" "(" CPackedArgData //result of #packArguments() : inargs, inargsize
                                     "," CTypedLLLExp   //address
                                     ")"    [seqstrict]

    rule <k> #ecallStmt(@argdata(CODE, _, SIZE), @tlll(_, ADDR, @none))
             => $%seq($assert($extcodesize(ADDR)),
                      $assert($ne($address, ADDR)),
                      $assert($staticcall($gas, ADDR, CODE, SIZE, 0, 0)), .LLLExps
                     ), .LLLExps
         ...</k>
         <constant> true </constant>

    rule <k> #ecallStmt(@argdata(CODE, _, SIZE), @tlll(_, ADDR, @none))
             => $%seq($assert($extcodesize(ADDR)),
                      $assert($ne($address, ADDR)),
                      $assert($call($gas, ADDR, 0, CODE, SIZE, 0, 0)), .LLLExps
                     ), .LLLExps
         ...</k>
         <constant> false </constant>


// Reserved Expr
// =============


    rule #compileToLoc(%balance(EXPR))    => #balance(#compileToVal(EXPR))

    syntax CTypedLLLExp  ::= "#balance" "(" CTypedLLLExp ")"  [strict]
 // ------------------------------------------------------------------
    rule #balance(@tlll(_:AddressType, ADDR, @none)) => @tlll(%unitT(%num, %wei |-> 1, false), $balance(ADDR), @none)


    rule #compileToLoc(%codesize(EXPR))   => #codesize(#compileToVal(EXPR))

    syntax CTypedLLLExp  ::= "#codesize" "(" CTypedLLLExp ")"   [strict]
 // --------------------------------------------------------------------
    rule #codesize(@tlll(_:AddressType, ADDR, @none)) => @tlll(%num, $extcodesize(ADDR), @none)


    rule #compileToLoc(%is_contract(EXPR)) => #is_contract(#compileToVal(EXPR))

    syntax CTypedLLLExp  ::= "#is_contract" "(" CTypedLLLExp ")"  [strict]
 // ----------------------------------------------------------------------
    rule #is_contract(@tlll(_:AddressType, ADDR, @none)) => @tlll(%bool, $extcodesize(ADDR), @none)


    rule #compileToLoc(%msg.sender)       => @tlll(%address, $caller, @none)

    rule #compileToLoc(%msg.value)        => @tlll(%unitT(%num, %wei |-> 1, false), $callvalue, @none)

    rule #compileToLoc(%msg.gas)          => @tlll(%num, $gas, @none)

    rule #compileToLoc(%block.difficulty) => @tlll(%num, $difficulty, @none)

    rule #compileToLoc(%block.timestamp)  => @tlll(%unitT(%num, %sec |-> 1, true), $timestamp, @none)

    rule #compileToLoc(%block.coinbase)   => @tlll(%address, $coinbase, @none)

    rule #compileToLoc(%block.number)     => @tlll(%num, $number, @none)

    rule #compileToLoc(%block.prevhash)   => @tlll(%bytes32, $blockhash($sub($number, 1)), @none)

    rule #compileToLoc(%tx.origin)        => @tlll(%address, $origin, @none)


// Reserved Function
// =================


    // floor
    //---------------------
    syntax CTypedLLLExp  ::= "#floor" "(" CTypedLLLExp ")"    [strict]
 // ------------------------------------------------------------------
    rule #compileToLoc(%floor(EXPR)) => #floor(#compileToVal(EXPR))

    rule #floor(@tlll(%decimal, CODE, @none))
        => @tlll(%num, $if($slt(CODE, 0),
                           $sdiv($sub( CODE, @decimalDivisor -Int 1), @decimalDivisor),
                           $sdiv(CODE, @decimalDivisor)
                       ), @none)

    rule #floor(@tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, @none))
         => #setType(#floor(@tlll(%decimal, CODE, @none)), %unitT(%decimal, UNITMAP:Map, POSITIONAL))


    // ceil
    //---------------------
    rule #compileToLoc(%ceil(EXPR)) => #ceil(#compileToVal(EXPR))

    syntax CTypedLLLExp  ::= "#ceil" "(" CTypedLLLExp ")"    [strict]
 // ------------------------------------------------------------------
    rule #ceil(@tlll(%decimal, CODE, @none))
         => @tlll(%num, $if($slt(CODE, 0),
                            $sdiv(CODE, @decimalDivisor),
                            $sdiv($add( CODE, @decimalDivisor -Int 1), @decimalDivisor)
                        ), @none)

    rule #ceil(@tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, @none))
         => #setType(#ceil(@tlll(%decimal, CODE, @none)), %unitT(%decimal, UNITMAP:Map, POSITIONAL))


    // decimal
    //---------------------
    syntax CTypedLLLExp  ::= "#decimal" "(" CTypedLLLExp ")"    [strict]
 // --------------------------------------------------------------------
    rule #compileToLoc(%decimal(EXPR)) => #decimal(#compileToVal(EXPR))

    rule #decimal(@tlll(%num, CODE, _))
        => @tlll(%decimal, $mul(CODE, @decimalDivisor), @none)

    rule #decimal(@tlll(%unitT(%num, UNITMAP:Map, POSITIONAL), CODE, _))
        => @tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), $mul(CODE, @decimalDivisor), @none)

    rule #decimal(@tlll(%decimal, CODE, _))
        => @tlll(%decimal, CODE, @none)

    rule #decimal(@tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, _))
        => @tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, @none)


    // as_unitless_number
    //---------------------
    syntax CTypedLLLExp  ::= "#asUnitlessNumber" "(" CTypedLLLExp ")"  [strict]
 // ---------------------------------------------------------------------------
    rule #compileToLoc(%as_unitless_number(EXPR)) => #asUnitlessNumber(#compileToVal(EXPR))

    rule #asUnitlessNumber(@tlll(%num, CODE, _)) => @tlll(%num, CODE, @none)

    rule #asUnitlessNumber(@tlll(%unitT(%num, UNITMAP:Map, POSITIONAL), CODE, _))
        => @tlll(%num, CODE, @none)

    rule #asUnitlessNumber(@tlll(%decimal, CODE, _)) => @tlll(%decimal, CODE, @none)

    rule #asUnitlessNumber(@tlll(%unitT(%decimal, UNITMAP:Map, POSITIONAL), CODE, _))
        => @tlll(%decimal, CODE, @none)


    // convert()
    //---------------------
    rule #compileToLoc(%convert(EXPR, TypeS)) => #convert(#compileToVal(EXPR), TypeS)
      requires notBool TypeS ==String "uint256" orBool notBool isInt(EXPR)

    rule #compileToLoc(%convert(I:Int, "uint256")) => #asNum256Number(I)


    syntax CTypedLLLExp ::= "#convert" "(" CTypedLLLExp "," String ")"    [strict(1)]
 // ------------------------------------------------------------------------
    rule #convert(@tlll(%unitT(T, _:Map,_) => T, CODE, LA), _)


    // convert(EXPR, "int128")
    //---------------------
    rule #convert(TLLL:TypedLLLExp, "int128") => #asNum128(TLLL)

    syntax CTypedLLLExp  ::= "#asNum128"    "(" CTypedLLLExp ")"    [strict]
 // ------------------------------------------------------------------------
    rule #asNum128(@tlll(T, CODE:LLLExp, LA))
         => @tlll(%num, $clamp($mload(@minNumPos), CODE, $mload(@maxNumPos)), @none)
      requires #isTypeOf(T, %num) orBool #isTypeOf(T, %num256) orBool #isTypeOf(T, %bytes32) orBool isAddressType(T)

    rule #asNum128(@tlll(T:ByteArrayType, CODE, LA)) => #byte_array_to_num(@tlll(T, CODE, LA), %num, 32)

    rule (. => #exception("Function arg type does not match expected type."))
         ~> #asNum128(@tlll(T, CODE:LLLExp, LA))
      requires notBool(#isTypeOf(T, %num) orBool #isTypeOf(T, %num256) orBool #isTypeOf(T, %bytes32)
                       orBool isAddressType(T) orBool isByteArrayType(T))

    syntax CTypedLLLExp  ::= "#byte_array_to_num"    "(" TypedLLLExp "," Type "," Int ")"
  // ------------------------------------------------------------------------
    rule #byte_array_to_num(@tlll(T:ByteArrayType, CODE:LLLExp, @locattr(LTGT:LocTarget, _)), OutT, Offset)
        => @tlll(OutT,
            $with($_sub, CODE,
                 $with($_el1, /*first_el_getter*/
                              #ifLLLExp(LTGT ==K @memory, $mload($add(32, $_sub)), $sload($add(1, $sha3_32($_sub)))),
                    $with($_len, $clamp(0, /*lengetter*/
                                           #ifLLLExp(LTGT ==K @memory, $mload($_sub), $sload($sha3_32($_sub))), 32),
                       $%seq(
                          $assert($or($iszero($_len), $div($_el1, $exp(256, 31)))),
                          #ifLLLExp(OutT ==K %num,
                              $clamp($mload(@minDecimalPos),
                                     $div($_el1, $exp(256, $sub(32, $_len))),
                                     $mload(@maxDecimalPos)),
                              //original is probably wrong, reporting an issue
                              //$div($_el1, $exp(256, $sub(Offset, $_len))) //OutT ==K %num256
                              $_el1 //OutT ==K %num256
                          )
                       )))),
            @none)


    // convert(EXPR, "uint256")
    //---------------------
    rule #convert(@tlll(T, CODE, @none), "uint256") =>#asNum256(@tlll(T, CODE, @none))

    syntax CTypedLLLExp  ::= "#asNum256Number" "(" Expr ")"
 // ---------------------------------------------------------
    rule #asNum256Number(I:Int) => #ifThenElse((I >=Int 0) andBool (I <=Int 2^Int 256 -Int 1),
                                               @tlll(%num256, I, @none),
                                               #exception("Number out of range") ~> #asNum256Number(I))

    syntax CTypedLLLExp  ::= "#asNum256"    "(" CTypedLLLExp ")"    [strict]
 // ------------------------------------------------------------------------
    rule #asNum256(@tlll(%num, CODE, @none)) => @tlll(%num256, $clampge(CODE, 0), @none)

    rule #asNum256(@tlll(%bytes32, CODE, @none)) => @tlll(%num256, CODE, @none)

    rule (. => #exception("Invalid input for uint256"))
         ~> #asNum256(@tlll(T:Type, CODE, _))
      requires notBool(T ==K %num orBool T ==K %bytes32)


    // convert(EXPR, "decimal")
    //---------------------
    rule #convert(TLLL:TypedLLLExp, "decimal") => #asDecimal(TLLL)

    syntax CTypedLLLExp  ::= "#asDecimal"    "(" CTypedLLLExp ")"    [strict]
 // ------------------------------------------------------------------------
    rule #asDecimal(@tlll(%num, CODE:LLLExp, LA)) => @tlll(%decimal, $mul(CODE, @decimalDivisor), @none)


    // convert(EXPR, "bytes32")
    //---------------------
    rule #convert(TLLL:TypedLLLExp, "bytes32") => #asBytes32(TLLL)

    syntax CTypedLLLExp  ::= "#asBytes32" "(" CTypedLLLExp ")"    [strict]
 // ----------------------------------------------------------------------
    rule #asBytes32(@tlll(T, CODE:LLLExp, LA))
         => @tlll(%bytes32, CODE, @none)
      requires #isTypeOf(T, %num) orBool #isTypeOf(T, %num256) orBool isAddressType(T)

    rule #asBytes32(@tlll(%bytesT(LEN:Int), CODE:LLLExp, @locattr(LTGT, MT)))
         => #ifThenElse(LEN =/=Int 32,
              #exception("Unable to convert bytes to bytes32")
                  ~> #asBytes32(@tlll(%bytesT(LEN:Int), CODE:LLLExp, @locattr(LTGT, MT))),
              #ifThenElse(LTGT ==K @memory,
                          @tlll(%bytes32, $mload($add(CODE, 32)), @none),
                          @tlll(%bytes32, $sload($add($sha3_32(CODE), 1)), @none)))


    rule (. => #exception("Function arg type does not match expected type."))
         ~> #asBytes32(@tlll(T, CODE, EXPRATTR))
      requires notBool (#isTypeOf(T, %num) orBool #isTypeOf(T, %num256)
                        orBool isAddressType(T) orBool isByteArrayType(T))


    // slice
    //---------------------
    syntax CTypedLLLExp  ::= "#slice" "(" CTypedLLLExp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict]
    syntax CTypedLLLExp  ::= "#sliceAux" "(" TypedLLLExp  ","  // bytes
                                             LLLExp       ","  // start
                                             LLLExp       ","  // length
                                             CTypedLLLExp      // placeholder
                                         ")"      [strict(4)]
 // -----------------------------------------------------------------------------------------------------
    rule #compileToLoc(%slice(EXPR, STARTEXPR, LENEXPR))
        => #slice(#compileToLoc(EXPR), #compileToVal(STARTEXPR), #compileToVal(LENEXPR))

    rule #slice(@tlll(%bytesT(L), BYTESCODE, EXPRATTR), @tlll(%num, START, _), @tlll(%num, LEN, _))
        => #sliceAux(@tlll(%bytesT(L), BYTESCODE, EXPRATTR), START, LEN,
                           #newPlaceholder(%bytesT(L +Int 32)))

    rule #sliceAux(@tlll(%bytesT(L), BYTESLOC, @locattr(@storage, MUTABLE)), START, LEN, PLACEHOLDER)
        => #sliceBytesByCopy(@tlll(%bytesT(L),
                                   $add($sha3_32(BYTESLOC), $add($div($_start, 32), 1)),  // first pos is the byte array length
                                   @locattr(@storage, MUTABLE)),
                             L, START, LEN, PLACEHOLDER, BYTESLOC)

    rule #sliceAux(@tlll(%bytesT(L), BYTESLOC, @locattr(TARGET, MUTABLE)), START, LEN, PLACEHOLDER)
        => #sliceBytesByCopy(@tlll(%bytesT(L),
                                  $add(BYTESLOC, $add($sub($_start, $mod($_start, 32)),32)),  // make sure the byte arrary after copy is still 32-byte aligned.
                                  @locattr(TARGET, MUTABLE)),
                             L, START, LEN, PLACEHOLDER, BYTESLOC)
      requires TARGET =/=K @storage


    syntax CTypedLLLExp  ::= "#sliceBytesByCopy" "(" TypedLLLExp ","  // source
                                                     Int         ","  // old max length
                                                     LLLExp      ","  // start
                                                     LLLExp      ","  // length
                                                     TypedLLLExp ","  // placeholder (destination)
                                                     LLLExp           // BYTESLOC
                                                 ")"


    syntax CTypedLLLExp  ::= "#sliceBytesByCopyAux" "(" CLLLExp  ","  // copier
                                                        Int      ","  // placeholder loc
                                                        LLLExp   ","  // start
                                                        LLLExp   ","  // length
                                                        Int      ","  // old max length
                                                        Int      ","  // new max length
                                                        LLLExp        // BYTESLOC
                                                     ")"  [strict(1)]
 // -----------------------------------------------------------------
    rule #sliceBytesByCopy(SOURCE, OLDMAXLEN, START, LEN, @tlll(T, PLACEHOLDERLOC, LOCATTR), BYTESLOC)
        => #sliceBytesByCopyAux(#mkByteSliceCopier(@tlll(T, PLACEHOLDERLOC +Int 32, LOCATTR),
                                                   SOURCE,
                                                   $add($_length, 32),
                                                   OLDMAXLEN),
                                PLACEHOLDERLOC, START, LEN, OLDMAXLEN, LEN, BYTESLOC)
      requires isInt(LEN)

    rule #sliceBytesByCopy(SOURCE, OLDMAXLEN, START, LEN, @tlll(T, PLACEHOLDERLOC, LOCATTR), BYTESLOC)
        => #sliceBytesByCopyAux(#mkByteSliceCopier(@tlll(T, PLACEHOLDERLOC +Int 32, LOCATTR),
                                                   SOURCE,
                                                   $add($_length, 32),
                                                   OLDMAXLEN),
                                PLACEHOLDERLOC, START, LEN, OLDMAXLEN, OLDMAXLEN, BYTESLOC)
      requires notBool isInt(LEN)

    rule #sliceBytesByCopyAux(COPIER, PLACEHOLDERLOC, START, LEN, OLDMAXLEN, NEWMAXLEN, BYTESLOC)
        => @tlll(%bytesT(NEWMAXLEN), $with($_start, START,
                                      $with($_length, LEN,
                                        $with($_opos, $add(PLACEHOLDERLOC, $mod($_start, 32)),
                                          $%seq(
                                            $assert($le($add($_start, $_length), $mload(BYTESLOC))),
                                            COPIER,
                                            $mstore($_opos, $_length),
                                            $_opos,.LLLExps)))), @locattr(@memory, true))

    // len - byte array length
    //---------------------
    rule #compileToLoc(%len(E:Expr)) => #len(#compileToLoc(E))

    syntax CTypedLLLExp  ::= "#len"    "(" CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------
    rule #len(@tlll(%bytesT(L), BYTESCODE:LLLExp, @locattr(@memory, _)))
         => @tlll(%num, $mload(BYTESCODE), @none)

    rule #len(@tlll(%bytesT(L), BYTESCODE:LLLExp, @locattr(@storage, _)))
         => @tlll(%num, $sload($sha3_32(BYTESCODE)), @none)


    // concat
    //---------------------
    rule #compileToLoc(%concat(Es:Exprs)) => #concat(#compileExprs(Es))

    syntax CTypedLLLExp  ::= "#concat"    "(" CTypedLLLExps ")"    [seqstrict]
 // ------------------------------------------------------------------------
    //#concat is divided into allocation of space for final array, then appending arguments to this space one by one.
    //Required to optimize gas consumption.
    rule #concat(Args:TypedLLLExps) => #appendByteArray(#alloc(0, Args), Args, $pass)

    syntax CTypedLLLExp  ::= "#alloc"    "(" Int "," TypedLLLExps ")"
 // ------------------------------------------------------------------------
    rule #alloc(SIZE:Int => SIZE +Int NextSize, @tlll(%bytesT(NextSize:Int), _,_) Rest:TypedLLLExps => Rest )

    rule #alloc(SIZE:Int => SIZE +Int 32, @tlll(%bytes32, _,_) Rest:TypedLLLExps => Rest )

    rule #alloc(SIZE:Int => SIZE +Int 4, @tlll(%methodIdT, _,_) Rest:TypedLLLExps => Rest )

    rule <k> #alloc(SIZE:Int, .TypedLLLExps) => @tlll(%bytesT(SIZE), REZ, @locattr(@memory, true)) ...</k>
         <nextMem> REZ:Int => REZ +Int #sizeOfType(%bytesT(SIZE)) </nextMem>


    /*Algorighm of concat(A,B) (Outdated, was used before for concat of strictly 2 byte arrays)
        - Allocate into Rez a number of bytes = 32 (for array len) + A.{static len} padded to multiple of 32
                                       + B.{static len} padded to multiple of 32 (to avoid overflow later)
            Cannot allocate dynamic length because LLL alloc macro is not implemented.
        - Set [Rez] = A.len + B.len
        - Copy into [Rez+32] -> [Rez+32+A.len] sequence [A+32] -> [A+32+A.len], in pieces of 32 bytes.
        - Copy into [Rez+32+A.len] -> [Rez+32+A.len+B.len] sequence [B+32] -> [B+32+B.len], in pieces of 32 bytes.
        - Return Rez, as a @memory value.

        Some hacks used because LLL-EVM doesnt' support memory allocation and loops with non-const number of iteration.
        We'll alloc and copy data based on static arrays sizes, rather than actual dynamic sizes.

        New comments:
        Arguments: allocated location wrapped into @tlll(), arguments to append, resulting code.
    */
    syntax CTypedLLLExp  ::= "#appendByteArray"    "(" CTypedLLLExp "," TypedLLLExps "," LLLExp ")"    [strict(1)]
 // ------------------------------------------------------------------------

    //Appends one %methodIdT argument.
    rule #appendByteArray(@tlll(%bytesT(_), REZLoc:Int, _),
                     @tlll(%methodIdT, FID:Int, @none) Rest:TypedLLLExps => Rest,
                     RezCode:LLLExp => $%seq(RezCode,
                     $%seq(
                         //copy the bytes
                         $mstore($add(REZLoc +Int 32, $mload(REZLoc)), FID *Int (2 ^Int 224)),

                         //update result size
                         $mstore(REZLoc, $add($mload(REZLoc), 4)),
                     .LLLExps), .LLLExps)
         )

    //Appends one %bytes32 argument.
    rule #appendByteArray(@tlll(%bytesT(_), REZLoc:Int, _),
                     @tlll(%bytes32, CODE:LLLExp, @none) Rest:TypedLLLExps => Rest,
                     RezCode:LLLExp => $%seq(RezCode,
                     $%seq(
                         //copy the bytes
                         $mstore($add(REZLoc +Int 32, $mload(REZLoc)), CODE),

                         //update result size
                         $mstore(REZLoc, $add($mload(REZLoc), 32)),
                     .LLLExps), .LLLExps)
         )

    //Appends one %bytest(_) argument from memory.
    rule #appendByteArray(@tlll(%bytesT(_), REZLoc:Int, _),
                     @tlll(%bytesT(SIZE:Int), CODE:LLLExp, @locattr(@memory, _)) Rest:TypedLLLExps => Rest,
                     RezCode:LLLExp => $%seq(RezCode,
             $with($_loc1, CODE, // _loc1 = CODE
                       $%seq(
                           //copy the bytes
                           $repeat(@freeLoopIndexPos, 0, #ceil32(SIZE) /Int 32,
                                   $mstore($add($add(REZLoc +Int 32, $mload(REZLoc)), $mul($mload(@freeLoopIndexPos), 32)),
                                           $mload($add($add($_loc1, 32), $mul($mload(@freeLoopIndexPos), 32))))),

                           //update result size
                           $mstore(REZLoc, $add($mload(REZLoc), $mload($_loc1))),
                           .LLLExps)
                       ), .LLLExps)
                     )
      requires SIZE >Int 0

    //Appends one %bytest(_) argument from storage.
    rule #appendByteArray(@tlll(%bytesT(_), REZLoc:Int, _),
                     @tlll(%bytesT(SIZE:Int), CODE:LLLExp, @locattr(@storage, _)) Rest:TypedLLLExps => Rest,
                     RezCode:LLLExp => $%seq(RezCode,
             $with($_loc1, $sha3_32(CODE), // _loc1 = CODE
                       $%seq(
                           //copy the bytes
                           $repeat(@freeLoopIndexPos, 0, #ceil32(SIZE) /Int 32,
                                   $mstore($add($add(REZLoc +Int 32, $mload(REZLoc)), $mul($mload(@freeLoopIndexPos), 32)),
                                           $sload($add($add($_loc1, 1), $mload(@freeLoopIndexPos))))),

                           //update result size
                           $mstore(REZLoc, $add($mload(REZLoc), $sload($_loc1))),
                           .LLLExps)
                       ), .LLLExps)
                     )
      requires SIZE >Int 0

    //appending empty string results in no action
    rule #appendByteArray(_, @tlll(%bytesT(0), _,_) Rest:TypedLLLExps => Rest, _)

    rule #appendByteArray(@tlll(%bytesT(RezSize:Int), REZLoc:Int, LA:LocAttr), .TypedLLLExps, CODE:LLLExp)
         => @tlll(%bytesT(RezSize), $%seq(CODE, REZLoc), LA)

    // keccak256
    //---------------------
    rule #compileToLoc(%keccak256(E) => %sha3(E))


    // method_id
    //---------------------
    rule #compileToLoc(%method_id(S:String)) => S ~> #computeFuncIdAux ~> #methodId

    syntax K ::= "#methodId"
    syntax BaseType ::= "%methodIdT"

    rule FID:Int ~> #methodId => @tlll(%methodIdT, FID, @none)


    // ecrecover
    //---------------------
    rule #compileToLoc(%ecrecover(E1, E2, E3, E4))
         => #ecrecover(#compileToVal(E1), #compileToVal(E2), #compileToVal(E3), #compileToVal(E4),
                       #newPlaceholder(%bytesT(128)))

    syntax CTypedLLLExp  ::= "#ecrecover" "(" CTypedLLLExp
                                          "," CTypedLLLExp
                                          "," CTypedLLLExp
                                          "," CTypedLLLExp
                                          "," CTypedLLLExp
                                          ")"               [seqstrict]
 // ------------------------------------------------------------------------
    rule #ecrecover(@tlll(%bytes32, C0, _), @tlll(%num256, C1, _), @tlll(%num256, C2, _), @tlll(%num256, C3, _),
                    @tlll(%bytesT(_), PLLOC, _))
         => @tlll(%address, $%seq($mstore(PLLOC, C0),
                                  $mstore($add(PLLOC, 32), C1),
                                  $mstore($add(PLLOC, 64), C2),
                                  $mstore($add(PLLOC, 96), C3),
                                  $pop($call(3000, 1, 0, PLLOC, 128, @freeVarPos, 32)),
                                  $mload(@freeVarPos)),
                  @none)


    // ecadd()
    //---------------------
    rule #compileToLoc(%ecadd(E1, E2))
         => #ecadd(#compileToVal(E1), #compileToVal(E2), #newPlaceholder(%bytesT(128)))

    syntax CTypedLLLExp  ::= "#ecadd" "(" CTypedLLLExp
                                      "," CTypedLLLExp
                                      "," CTypedLLLExp
                                      ")"               [seqstrict]
 // ------------------------------------------------------------------------
    rule #ecadd(@tlll(%listT(%num256, 2), C0, LA0), @tlll(%listT(%num256, 2), C1, LA1), @tlll(%bytesT(128), PLLOC, _))
         => @tlll(%listT(%num256, 2),
                  $%seq($mstore( PLLOC, #getLLL(#unwrapLoc(
                                          #lookupListElementAux(@tlll(%listT(%num256, 2), C0, LA0),
                                                                @tlll(%num, 0, @none))))) /*avo(args[0], 0)*/,
                        $mstore( $add( PLLOC, 32), #getLLL(#unwrapLoc(
                                          #lookupListElementAux(@tlll(%listT(%num256, 2), C0, LA0),
                                                                @tlll(%num, 1, @none))))) /*avo(args[0], 1)*/,
                        $mstore( $add( PLLOC, 64), #getLLL(#unwrapLoc(
                                          #lookupListElementAux(@tlll(%listT(%num256, 2), C1, LA1),
                                                                @tlll(%num, 0, @none))))) /*avo(args[1], 0)*/,
                        $mstore( $add( PLLOC, 96), #getLLL(#unwrapLoc(
                                          #lookupListElementAux(@tlll(%listT(%num256, 2), C1, LA1),
                                                                @tlll(%num, 1, @none))))) /*avo(args[1], 1)*/,
                        $assert( $call( 500, 6, 0, PLLOC, 128, PLLOC, 64)),
                        PLLOC),
                  @locattr(@memory, false))


    // ecmul()
    //---------------------
    rule #compileToLoc(%ecmul(E1, E2))
         => #ecmul(#compileToVal(E1), #compileToVal(E2), #newPlaceholder(%bytesT(128)))

    syntax CTypedLLLExp  ::= "#ecmul" "(" CTypedLLLExp
                                      "," CTypedLLLExp
                                      "," CTypedLLLExp
                                      ")"               [seqstrict]
 // ------------------------------------------------------------------------
    rule #ecmul(@tlll(%listT(%num256, 2), C0, LA0), @tlll(%num256, C1, @none), @tlll(%bytesT(128), PLLOC, _))
         => @tlll(%listT(%num256, 2),
                  $%seq($mstore(PLLOC, #getLLL(#unwrapLoc(
                                          #lookupListElementAux(@tlll(%listT(%num256, 2), C0, LA0),
                                                                @tlll(%num, 0, @none))))) /*avo(args[0], 0)*/,
                        $mstore($add(PLLOC, 32), #getLLL(#unwrapLoc(
                                          #lookupListElementAux(@tlll(%listT(%num256, 2), C0, LA0),
                                                                @tlll(%num, 1, @none))))) /*avo(args[0], 1)*/,
                        $mstore($add(PLLOC, 64), C1),
                        $assert($call(40000, 7, 0, PLLOC, 96, PLLOC, 64)),
                        PLLOC),
                  @locattr(@memory, false))


    // extract32
    //---------------------
    rule #compileToLoc(%extract32(BExp, IExp, %num)) => #compileToLoc(%convert(%extract32(BExp, IExp, %bytes32), "int128"))

    rule #compileToLoc(%extract32(BExp, IExp, _:AddressType))
         => #toAddress(#extract32(#compileToVal(BExp), #compileToVal(IExp), %bytes32))

    rule #compileToLoc(%extract32(BExp, IExp, T:Type)) => #extract32(#compileToVal(BExp), #compileToVal(IExp), T)
      when T ==K %bytes32 orBool T ==K %num256

    syntax CTypedLLLExp  ::= "#extract32" "(" CTypedLLLExp "," CTypedLLLExp "," Type ")"    [seqstrict(1,2)]
 // ------------------------------------------------------------------------
    rule #extract32(@tlll(%bytesT(_), SUB:LLLExp, @locattr(LocTarg:LocTarget, _)),
                    @tlll(%num, INDEX:Int, @none), T:Type)
         => @tlll(T, $with($_sub, SUB, #extract32ElemGetter($div($clamp(0, INDEX,
                                          $sub(#extract32LenGetter(LocTarg), 32)), 32), LocTarg)), @none)
      requires INDEX %Int 32 ==Int 0

    rule #extract32(@tlll(%bytesT(_), SUB:LLLExp, @locattr(LocTarg:LocTarget, _)),
                    @tlll(%num, INDEX:LLLExp, @none), T:Type)
         => @tlll(T, $with($_sub, SUB,
                       $with($_len, #extract32LenGetter(LocTarg),
                        $with($_index, $clamp(0, INDEX, $sub($_len, 32)),
                         $with($_mi32, $mod($_index, 32),
                          $with($_di32, $div($_index, 32),
                           $if(
                            $_mi32,
                            $add(
                             $mul(
                              #extract32ElemGetter($_di32, LocTarg),
                              $exp(256, $_mi32)),
                             $div(
                              #extract32ElemGetter($add($_di32, 1), LocTarg),
                              $exp(256, $sub(32, $_mi32)))),
                            #extract32ElemGetter($_di32, LocTarg))))))), @none)
      requires (notBool isInt(INDEX)) orBool (asInt(INDEX) %Int 32 =/=Int 0)

    syntax LLLExp ::= #extract32ElemGetter ( LLLExp , LocTarget )   [function]
 // ------------------------------------------------------------------------
    rule #extract32ElemGetter(INDEX, @memory)
         => $mload($add($_sub, $add(32, $mul(32, INDEX))))

    rule #extract32ElemGetter(INDEX, @storage)
         => $sload($add($sha3_32($_sub), $add(1, INDEX)))

    syntax LLLExp ::= #extract32LenGetter ( LocTarget )             [function]
 // ------------------------------------------------------------------------
    rule #extract32LenGetter(@memory) => $mload($_sub)

    rule #extract32LenGetter(@storage) => $sload($sha3_32($_sub))


    //Checks that value produced by CODE is inside the range for %address.
    syntax CTypedLLLExp  ::= "#toAddress" "(" CTypedLLLExp ")"    [strict]
 // ------------------------------------------------------------------------
    rule #toAddress(@tlll(T, CODE, @none)) => @tlll(%address, $uclamplt(CODE, $mload(@addrSizePos)), @none)


    // bytes_to_num
    //---------------------
    syntax CTypedLLLExp  ::= "#bytes_to_num"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp  ::= "#bytes_to_num_Aux" "(" LLLExp ")"
 // ------------------------------------------------------------------------
    rule #compileToLoc(%bytes_to_num(EXPR)) => #bytes_to_num(#compileToLoc(EXPR))

    rule #bytes_to_num(@tlll(T, LOC, @locattr(@memory, B)))
        => #ifThenElse(isByteArrayType(T),
                       #bytes_to_num_Aux(LOC),
                       #exception("Function arg type does not match expected type.")
                          ~> #bytes_to_num(@tlll(T, LOC, @locattr(@memory, B))))

    /*Conversion algorithm:
        Allocate 64 bytes to some V.
        Check that most significant byte in the array is not 0x00.
        Initialzie first 32 bytes with the correct padding: 0x00 if nonnegative, 0xff if negative.
        Copy the block starting with LOC+32 to position V+32-[byte array size].
            This way the useful [byte array size] bites will be the last in the block V -> V+32.
        Return block V.

        Alternative implementation:
            allocate only 32 bytes and copy the useful bytes one by one in a loop using $mstore8 .

        Byte array format in memory: First 32 bytes (from LOC): SIZE,
                                     next SIZE bytes: the actual bytes. (padded with 0x00 to full blocks of 32 bytes)
        bytes example:    1234000000. Useful bytes position: LOC+32 -> LOC+32 + *LOC
        int128 equiv :    xxxxxx1234  Useful bytes position: LOC+64 - *LOC -> LOC+64
    */
    rule <k> #bytes_to_num_Aux(LOC:LLLExp)
            => @tlll(%num,
                     $with($_loc, LOC, // _loc = LOC
                           $if($iszero($mload(LOC)), 0,
                               $%seq(
                                   //checking that most significant byte is not 0x00
                                   $assert($byte(0, $mload($add($_loc, 32)))),

                                   $mstore(V, 0),
                                   $mstore($add(V, $sub(32, $mload(LOC))), $mload($add($_loc, 32))),

                                   //re-writing everything with padding 0xff if number is negative
                                   $if($gt($mload(V), @maxNum),
                                        $seq($mstore(V, -1),
                                             $mstore($add(V, $sub(32, $mload(LOC))), $mload($add($_loc, 32))))),
                                   $mload(V),
                                   .LLLExps)
                           )),
                     @none)
         ...</k>
         <nextMem> V:Int => V +Int 64 </nextMem>


    // as_wei_value
    syntax CTypedLLLExp  ::= "#asWeiValue" "(" Expr "," K ")"    [strict(2)]
 // ------------------------------------------------------------------------
    rule #compileToLoc(%as_wei_value(EXPR, UNIT)) => #asWeiValue(EXPR, #convertToWei(UNIT))

    rule #asWeiValue(NUM:Const, DENOMINATION)
        => #asWeiValueNumber(NUM, DENOMINATION)

    rule #asWeiValue(EXPR, DENOMINATION)
        => #asWeiValueLLLExp(#compileToVal(EXPR), DENOMINATION)
      requires notBool isConst(EXPR)


    syntax CTypedLLLExp  ::= "#asWeiValueNumber" "(" Const        "," Int ")"
    syntax CTypedLLLExp  ::= "#asWeiValueLLLExp" "(" CTypedLLLExp "," Int ")"  [strict(1)]
 // --------------------------------------------------------------------------------------
    rule #asWeiValueNumber(NUM:Int, DENOMINATION:Int)
        => @tlll(%unitT(%num, %wei |-> 1, false), NUM *Int DENOMINATION, @none)

    rule #asWeiValueNumber(%fixed10(NUM, DEN), DENOMINATION)
        => #ifThenElse((DENOMINATION modInt DEN) =/=Int 0,
                       #exception("Too many decimal places.") ~> #asWeiValueNumber(%fixed10(NUM, DEN), DENOMINATION),
                       @tlll(%unitT(%num, %wei |-> 1, false), (NUM *Int DENOMINATION) /Int DEN, @none))

    rule #asWeiValueLLLExp(@tlll(%num, CODE, EXPRATTR), DENOMINATION)
        => @tlll(%unitT(%num, %wei |-> 1, false), $mul(CODE, DENOMINATION), @none)

    rule #asWeiValueLLLExp(@tlll(%decimal, CODE, EXPRATTR), DENOMINATION)
        => @tlll(%unitT(%num, %wei |-> 1, false), $div($mul(CODE, DENOMINATION), @decimalDivisor), @none)


    // raw_call()
    //==========================================
    rule #compileToLoc(%raw_call(E1, E2, I3:Int, E4, E5)) => #raw_call(#compileToVal(E1),
                                                                       #compileToVal(E2),
                                                                       I3,
                                                                       #compileToVal(E4),
                                                                       #compileToVal(E5))

    syntax CTypedLLLExp ::= "#raw_call" "(" CTypedLLLExp    // address
                                        "," CTypedLLLExp    // data: Bytes
                                        "," Int             // outsize
                                        "," CTypedLLLExp    // gas: int128
                                        "," CTypedLLLExp    // value: int128 optional
                                        ")"  [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule <k> (. => #exception("Cannot make calls from a constant function"))
             ~> #raw_call(_,_,_,_,_) ...</k>
         <constant> true </constant>

    rule <k> #raw_call(TL1:TypedLLLExp, @tlll(DataT, DataCODE, DataLA), OUTSIZE, TL4:TypedLLLExp,
                       @tlll(ValT, ValCODE, @none))
         => #ifThenElse(#areUnitsCompatible(ValT, %unitT(%num, %wei |-> 1, false), false),
                        #raw_call2(TL1, @tlll(DataT, DataCODE, DataLA), OUTSIZE, TL4, @tlll(ValT, ValCODE, @none),
                                   #newPlaceholder(DataT)),
                        #exception("Invalid units for value")
                          ~> #raw_call(TL1, @tlll(DataT, DataCODE, DataLA), OUTSIZE, TL4, @tlll(ValT, ValCODE, @none))
            ) ...</k>
         <constant> false </constant>

    /*  copier = make_byte_array_copier(placeholder_node, data)
        output_placeholder = context.new_placeholder(ByteArrayType(outsize))
    */
    syntax CTypedLLLExp ::= "#raw_call2" "(" TypedLLLExp      // address
                                         "," TypedLLLExp      // data: Bytes
                                         "," Int              // outsize
                                         "," TypedLLLExp      // gas: int128
                                         "," TypedLLLExp      // value: int128 optional
                                         "," CTypedLLLExp     // placeholder
                                         ")"  [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #raw_call2(TL1, TL2, OUTSIZE, TL4, TL5, PL:TypedLLLExp)
         => #raw_call3(TL1, OUTSIZE, TL4, TL5, PL, #mkByteArrayCopier(PL, TL2), #newPlaceholder(%bytesT(OUTSIZE)))

    /* z = LLLnode.from_list(['seq',
                              copier,
                              ['assert', ['call', gas, to, value, ['add', placeholder_node, 32], ['mload', placeholder_node],
                                         ['add', output_node, 32], outsize]],
                              ['mstore', output_node, outsize],
                              output_node], typ=ByteArrayType(outsize), location='memory', pos=getpos(expr))
    */
    syntax CTypedLLLExp ::= "#raw_call3" "(" TypedLLLExp      // address
                                         "," Int              // outsize
                                         "," TypedLLLExp      // gas: int128
                                         "," TypedLLLExp      // value: int128 optional
                                         "," TypedLLLExp      // placeholder
                                         "," CLLLExps         // copier
                                         "," CTypedLLLExp     // output_placeholder
                                         ")"  [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #raw_call3(@tlll(_, AddrCODE, _),
                    OUTSIZE,
                    @tlll(_, GasCODE, _),
                    @tlll(_, ValCode, _),
                    @tlll(_, PLCode, _),
                    COPIER:LLLExp,.LLLExps,
                    @tlll(_, OutPLCode, _))
         => @tlll(%bytesT(OUTSIZE), $%seq(COPIER,
                                          $assert($call(GasCODE, AddrCODE, ValCode, $add(PLCode, 32), $mload(PLCode),
                                                        $add(OutPLCode, 32), OUTSIZE)),
                                          $mstore(OutPLCode, OUTSIZE),
                                          OutPLCode), @locattr(@memory, true))


    // create_with_code_of()
    //==========================================
    rule #compileToLoc(%create_with_code_of(E1, E2)) => #create_with_code_of(#compileToVal(E1),
                                                                             #compileToVal(E2))

    syntax CTypedLLLExp ::= "#create_with_code_of" "(" CTypedLLLExp    // address
                                                   "," CTypedLLLExp    // value: int128 optional
                                                   ")"  [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule <k> (. => #exception("Cannot make calls from a constant function"))
             ~> #create_with_code_of(_,_) ...</k>
         <constant> true </constant>

    rule <k> #create_with_code_of(TL1:TypedLLLExp, @tlll(ValT, ValCODE, @none))
         => #ifThenElse(#areUnitsCompatible(ValT, %unitT(%num, %wei |-> 1, false), false),
                        #create_with_code_of2(TL1, @tlll(ValT, ValCODE, @none),
                                              #newPlaceholder(%bytesT(96))),
                        #exception("Invalid units for value")
                          ~> #create_with_code_of(TL1:TypedLLLExp, @tlll(ValT, ValCODE, @none))
            ) ...</k>
         <constant> false </constant>

    syntax CTypedLLLExp ::= "#create_with_code_of2" "(" TypedLLLExp      // address
                                                    "," TypedLLLExp      // value: int128 optional
                                                    "," CTypedLLLExp     // placeholder
                                                    ")"  [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #create_with_code_of2(@tlll(%address, AddrCODE, @none), @tlll(_, ValCODE, @none), @tlll(_, PLLoc:Int, _))
         => @tlll(%address,
                  $%seq($mstore(PLLoc, #create_wco_high),
                        $mstore($add( PLLoc, 27), $mul(AddrCODE, 2 ^Int 96)),
                        $mstore($add( PLLoc, 47), #create_wco_low),
                        $clamp_nonzero($create(ValCODE, PLLoc, 64))),
                  @none)

    syntax String ::= "#create_wco_kode"  [function]
    //len 58 + 21
    rule #create_wco_kode => "`.`\x0c`\x009`.`\x00\xf36`\x00`\x007a\x10\x00`\x006`\x00s\x00\x00\x00\x00\x00\x00"
         +String "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00Z\xf4\x15XWa\x10\x00`\x00\xf3"
         +String "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

    syntax Int ::= "#create_wco_high"  [function]
    rule #create_wco_high => #string2BytesInt(substrString(#create_wco_kode, 0, 32))

    syntax Int ::= "#create_wco_low"  [function]
    rule #create_wco_low => #string2BytesInt(substrString(#create_wco_kode, 47, 79))


    // blockhash
    //==========================================
    rule #compileToLoc(%blockhash(EXPR)) => #blockhash(#compileToVal(EXPR))

    syntax CTypedLLLExp  ::= "#blockhash" "(" CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #blockhash(@tlll(%num, CODE, @none))
         => @tlll(%bytes32, $blockhash($uclamplt($clampge(CODE, $sub($number, 256)), $number)), @none)


    // bitwise_and
    //==========================================
    syntax CTypedLLLExp  ::= "#bitwise_and" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%bitwise_and(EXPR1, EXPR2)) => #bitwise_and(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #bitwise_and(@tlll(_, CODE1, _), @tlll(_, CODE2, _))
        => @tlll(%num256, $and(CODE1, CODE2), @none)


    // bitwise_or
    syntax CTypedLLLExp  ::= "#bitwise_or" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%bitwise_or(EXPR1, EXPR2)) => #bitwise_or(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #bitwise_or(@tlll(_, CODE1, _), @tlll(_, CODE2, _))
        => @tlll(%num256, $or(CODE1, CODE2), @none)


    // bitwise_xor
    syntax CTypedLLLExp  ::= "#bitwise_xor" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%bitwise_xor(EXPR1, EXPR2)) => #bitwise_xor(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #bitwise_xor(@tlll(_, CODE1, _), @tlll(_, CODE2, _))
        => @tlll(%num256, $xor(CODE1, CODE2), @none)


    // bitwise_not
    syntax CTypedLLLExp  ::= "#bitwise_not" "(" CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%bitwise_not(EXPR1)) => #bitwise_not(#compileToVal(EXPR1))

    rule #bitwise_not(@tlll(_, CODE1, _))
        => @tlll(%num256, $not(CODE1), @none)


    // uint256_add
    syntax CTypedLLLExp  ::= "#num256Add" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_add(EXPR1, EXPR2)) => #num256Add(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Add(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($ge($add(CODE1, CODE2), CODE1)),
                            $add(CODE1, CODE2),.LLLExps), @none)


    // uint256_sub
    syntax CTypedLLLExp  ::= "#num256Sub" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_sub(EXPR1, EXPR2)) => #num256Sub(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Sub(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($ge(CODE1, CODE2)),
                            $sub(CODE1, CODE2),.LLLExps), @none)


    // uint256_mul
    syntax CTypedLLLExp  ::= "#num256Mul" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_mul(EXPR1, EXPR2)) => #num256Mul(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Mul(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($or($iszero(CODE1), $eq($div($mul(CODE1, CODE2), CODE1), CODE2))),
                            $mul(CODE1, CODE2),.LLLExps), @none)


    // uint256_div
    syntax CTypedLLLExp  ::= "#num256Div" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_div(EXPR1, EXPR2)) => #num256Div(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Div(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $div(CODE1, $clamp_nonzero(CODE2)), @none)


    // uint256_exp
    syntax CTypedLLLExp  ::= "#num256Exp" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_exp(EXPR1, EXPR2)) => #num256Exp(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Exp(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($or($or($eq(CODE2, 1), $iszero(CODE2)), $lt(CODE1, $exp(CODE1, CODE2)))),
                            $exp(CODE1, CODE2),.LLLExps), @none)


    // uint256_mod
    syntax CTypedLLLExp  ::= "#num256Mod" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_mod(EXPR1, EXPR2)) => #num256Mod(#compileToVal(EXPR1), #compileToVal(EXPR2))

    // ['mod', args[0], args[1]]
    rule #num256Mod(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $mod(CODE1, $clamp_nonzero(CODE2)), @none)


    // uint256_addmod
    syntax CTypedLLLExp  ::= "#num256Addmod" "(" CTypedLLLExp "," CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_addmod(EXPR1, EXPR2, EXPR3)) 
         => #num256Addmod(#compileToVal(EXPR1), #compileToVal(EXPR2), #compileToVal(EXPR3))

    /*return LLLnode.from_list(['seq',
                                  ['assert', ['or', ['iszero', args[1]], ['gt', ['add', args[0], args[1]], args[0]]]],
                                  ['addmod', args[0], args[1], args[2]]], typ=BaseType('num256'), pos=getpos(expr))    
    */
    rule #num256Addmod(@tlll(%num256, CODE0, _), @tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq(
                            $assert($or($iszero(CODE1), $gt($add(CODE0, CODE1), CODE0))),
                            $addmod(CODE0, CODE1, $clamp_nonzero(CODE2)),.LLLExps), @none)
                            
                            
    // uint256_mulmod
    syntax CTypedLLLExp  ::= "#num256Mulmod" "(" CTypedLLLExp "," CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_mulmod(EXPR1, EXPR2, EXPR3))
         => #num256Mulmod(#compileToVal(EXPR1), #compileToVal(EXPR2), #compileToVal(EXPR3))

    /*return LLLnode.from_list(['seq',
                            ['assert', ['or', ['iszero', args[0]],
                            ['eq', ['div', ['mul', args[0], args[1]], args[0]], args[1]]]],
                            ['mulmod', args[0], args[1], args[2]]], typ=BaseType('num256'), pos=getpos(expr))    
    */
    rule #num256Mulmod(@tlll(%num256, CODE0, _), @tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%num256, $%seq($assert($or($iszero(CODE0),
                                            $eq($div($mul(CODE0, CODE1), CODE0), CODE1))),
                                $mulmod(CODE0, CODE1, $clamp_nonzero(CODE2))), @none)


    // uint256_gt
    syntax CTypedLLLExp  ::= "#num256Gt" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // -----------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_gt(EXPR1, EXPR2)) => #num256Gt(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Gt(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%bool, $gt(CODE1, CODE2), @none)


    // uint256_ge
    syntax CTypedLLLExp  ::= "#num256Ge" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // -----------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_ge(EXPR1, EXPR2)) => #num256Ge(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Ge(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%bool, $ge(CODE1, CODE2), @none)


    // uint256_lt
    syntax CTypedLLLExp  ::= "#num256Lt" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // -----------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_lt(EXPR1, EXPR2)) => #num256Lt(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Lt(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%bool, $lt(CODE1, CODE2), @none)


    // uint256_le
    syntax CTypedLLLExp  ::= "#num256Le" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // -----------------------------------------------------------------------------------------
    rule #compileToLoc(%uint256_le(EXPR1, EXPR2)) => #num256Le(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #num256Le(@tlll(%num256, CODE1, _), @tlll(%num256, CODE2, _))
        => @tlll(%bool, $le(CODE1, CODE2), @none)


    // shift
    // If second argument is positive, left-shift so multiply by a power of two
    // If it is negative, divide by a power of two
    syntax CTypedLLLExp  ::= "#shift" "(" CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict]
 // ------------------------------------------------------------------------------------------
    rule #compileToLoc(%shift(EXPR1, EXPR2)) => #shift(#compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #shift(@tlll(%num256, CODE1, _), @tlll(%num, CODE2, _))
        => @tlll(%num256,
            $if($sle(CODE2, 0),
                $div(CODE1, $exp(2, $sub(0, CODE2))),
                $mul(CODE1, $exp(2, CODE2))
        ), @none)


    // min, max
    //type compatibility: num with decimal, num256 only with num256.
    syntax CTypedLLLExp  ::= "#minMax"    "(" CompareOp "," CTypedLLLExp "," CTypedLLLExp ")"    [seqstrict(2,3)]
    syntax CTypedLLLExp  ::= "#minMaxAux" "(" CompareOp ","  TypedLLLExp ","  TypedLLLExp ")"
 // -------------------------------------------------------------------------------------------
    rule #compileToLoc(%min(EXPR1, EXPR2)) => #minMax(%le, #compileToVal(EXPR1), #compileToVal(EXPR2))
    rule #compileToLoc(%max(EXPR1, EXPR2)) => #minMax(%ge, #compileToVal(EXPR1), #compileToVal(EXPR2))

    rule #minMax(OP, @tlll(LT, LCODE, LEXPRATTR), @tlll(RT, RCODE, REXPRATTR))
        => #ifThen(notBool(#isTypeOf(LT, %num) orBool #isTypeOf(LT, %decimal) orBool #isTypeOf(LT, %num256)) orBool
                   notBool(#isTypeOf(RT, %num) orBool #isTypeOf(RT, %decimal) orBool #isTypeOf(RT, %num256)),
                   #exception("Function arg type does not match expected type."))
        ~> #ifThen(notBool(#areUnitsCompatible(LT, RT, #isNumLiteral(LCODE))) andBool
                   notBool(#areUnitsCompatible(RT, LT, #isNumLiteral(RCODE))),
                   #exception("Units must be compatible."))
        ~> #minMaxAux(OP, @tlll(#dropUnit(LT), LCODE, LEXPRATTR),
                          @tlll(#dropUnit(RT), RCODE, REXPRATTR))

    rule #minMaxAux(OP, @tlll(T1, CODE1, A1), @tlll(T2, CODE2, A2))
        => #ifThen(notBool(
                    (isPureNumType(T1) andBool isPureNumType(T2))
                    orBool (T1 ==K %num256 andBool T2 ==K %num256)),
                    #exception("Minmax types incompatible."))
        ~> #ifThenElse(T1 ==K %num256,
                       @tlll(%num256, $if( #ifLLLExp(OP ==K %le, $le(CODE1, CODE2), $ge(CODE1, CODE2)),
                                            CODE1, CODE2), @none),
                       #tlllAux(#joinType(T1, T2),
                                #ifstmt(#compareOp(OP, @tlll(T1, CODE1, A1), @tlll(T2, CODE2, A2)),
                                        CODE1,.LLLExps, CODE2,.LLLExps),
                                @none)
                       )

    // TODO: figure out the result type containing unit or not.

    syntax CTypedLLLExp  ::= "#tlllAux"  "(" Type              ","
                                             CLLLExps          ","  //have to make it Exps, not Exp, to support #ifstmt
                                             LLLExpAttr        ")"  [strict(2)]

    rule #tlllAux(T, (Exp:LLLExp, .LLLExps), A) => @tlll(T, Exp, A)

    syntax LLLExp ::= #getLLL ( TypedLLLExp )   [function]
    rule #getLLL(@tlll(_, CODE, _)) => CODE

    //Wrapper over builtin #if, of sort LLLExp
    syntax LLLExp ::= "#ifLLLExp" "(" K "," K "," K ")"             [function]

    rule #ifLLLExp(K1, K2, K3) => #if K1 #then K2 #else K3 #fi


    /* sha3
      impl: functions.py : _sha3
    */
    syntax CTypedLLLExp  ::= "#sha3" "(" CTypedLLLExp ")"    [strict]
 // -----------------------------------------------------------------------------------------
    rule #compileToLoc(%sha3(EXPR)) => #sha3(#compileToVal(EXPR))

    rule #sha3(@tlll(T:Type, CODE, LocAttr:LLLExpAttr))
        => #ifThenElse(T ==K %bytes32,
              //This implementation is not equivalent to below. But should be. test_sha3.py fails. Why??
              //@tlll(%bytes32, $sha3_32(CODE), @none),
              //['seq', ['mstore', MemoryPositions.FREE_VAR_SPACE, sub], ['sha3', MemoryPositions.FREE_VAR_SPACE, 32]]
              @tlll(%bytes32, $%seq($mstore(@freeVarPos, CODE), $sha3(@freeVarPos, 32)), @none),

              #ifThenElse(isByteArrayType(T),
                #ifThenElse(#isInMemory(LocAttr),
                  // ['with', '_sub', sub, ['sha3', ['add', '_sub', 32], ['mload', '_sub']]], typ=BaseType('bytes32')
                  @tlll(%bytes32,
                        $with($_sub, CODE, $sha3($add($_sub, 32), $mload($_sub))),
                        @none),
                  #ifThenElse(#isStorage(LocAttr),
                    #sha3_ByteArray_storage(@tlll(T, CODE, LocAttr), #newPlaceholder(T)),
                    #exception("sha3: Unsupported location.") ~> #sha3(@tlll(T:Type, CODE, LocAttr))
                  )
                ),
                #exception("Expecting one of ('str_literal', 'bytes', 'bytes32') for argument 1 of sha3")
                  ~> #sha3(@tlll(T:Type, CODE, LocAttr))
              )
           )

    /* lengetter = LLLnode.from_list(['sload', ['sha3_32', '_sub']], typ=BaseType('num'))
       placeholder = context.new_placeholder(sub.typ) (already allocated above)
       placeholder_node = LLLnode.from_list(placeholder, typ=sub.typ, location='memory')
       copier = make_byte_array_copier(placeholder_node, LLLnode.from_list('_sub', typ=sub.typ, location=sub.location))
       return:
        ['with', '_sub', sub, ['seq', copier, ['sha3', ['add', placeholder, 32], lengetter]]], typ=BaseType('bytes32')
    */
    syntax CTypedLLLExp  ::= "#sha3_ByteArray_storage" "(" TypedLLLExp  //%sha3 argument code
                                                       "," CTypedLLLExp //placeholder - allocated temp memory buffer
                                                       ")"    [strict]
                           | "#sha3_ByteArray_storageAux" "(" TypedLLLExp   //%sha3 argument code
                                                          "," TypedLLLExp   //placeholder - allocated temp memory buffer
                                                          "," CLLLExps      //make_byte_array_copier(...)
                                                          ")" [strict]

    rule #sha3_ByteArray_storage(@tlll(T:Type, CODE, LocAttr:LLLExpAttr), Placeholder:TypedLLLExp)
         => #sha3_ByteArray_storageAux(@tlll(T, CODE, LocAttr),
                                       Placeholder,
                                       #mkByteArrayCopier(Placeholder, @tlll(T, $_sub, LocAttr)))

    rule #sha3_ByteArray_storageAux(@tlll(_, CODE:LLLExp, _), @tlll(_, PL:LLLExp, _), CopierCODE:LLLExps)
         => @tlll(%bytes32,
              $with($_sub, CODE,
                $%seq(
                  CopierCODE ++LLL
                  $sha3($add(PL, 32), $sload($sha3_32($_sub))), .LLLExps
                )
              ), @none)

//////////////////////////////////////////////////////////////////////////////
// Utils
//////////////////////////////////////////////////////////////////////////////


    syntax Bool  ::= "#isInitFunc" "(" Id ")"    [function]
 // -------------------------------------------------------
    rule #isInitFunc(FNAME) => FNAME ==K __init__


    syntax Bool  ::= "#isTypeOf" "(" Type "," Type /*target type*/ ")"    [function]
 // --------------------------------------------------------------------------------
    rule #isTypeOf(%unitT(T, _:Map, _), TARGET) => T ==K TARGET

    rule #isTypeOf(T, TARGET) => T ==K TARGET
      requires notBool isUnitType(T)


    syntax Bool  ::= "#isTopic" "(" EventParam ")"    [function]
 // ------------------------------------------------------------
    rule #isTopic(%eparam(_, _, ISTOPIC)) => ISTOPIC


    syntax Bool  ::= "#isInMemory" "(" LLLExpAttr ")"    [function]
 // ---------------------------------------------------------------
    rule #isInMemory(@locattr(@memory, _)) => true

    rule #isInMemory(@locattr(@storage, _)) => false

    rule #isInMemory(@locattr(@storage_prehashed, _)) => false

    rule #isInMemory(@none) => false


    syntax Bool  ::= "#isStorage" "(" LLLExpAttr ")"    [function]
 // ---------------------------------------------------------------
    rule #isStorage(@locattr(@memory, _)) => false

    rule #isStorage(@locattr(@storage, _)) => true

    rule #isStorage(@locattr(@storage_prehashed, _)) => false

    rule #isStorage(@none) => false


    syntax Bool  ::= "#isNumLiteral" "(" LLLExp ")"  [function]
 // -----------------------------------------------------------
    rule #isNumLiteral(CODE) => isInt(CODE) orBool isFixedPoint(CODE)


    syntax Type ::= "#joinType" "(" Type "," Type ")"              [function]
 // -----------------------------------------------------------

    rule #joinType(_:PureNumType, %decimal) => %decimal
    rule #joinType(%decimal, _:PureNumType) => %decimal
    rule #joinType(%num, %num)              => %num


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

    rule (EXPR:Expr EXPRS1:Exprs) ++Expr EXPRS2:Exprs => (EXPR (EXPRS1 ++Expr EXPRS2)):Exprs


    syntax LLLExp   ::= "$%seq" "(" LLLExps ")"    [function]
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

    rule #inDecorators(DEC, DEC DECS) => true

    rule #inDecorators(D, (DEC DECS => DECS))
      requires D =/=K DEC


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


    syntax Int  ::= "#sizeOfEParams" "(" EventParams ")"    [function]
 // ------------------------------------------------------------
    rule #sizeOfEParams(.EventParams) => 0
    rule #sizeOfEParams(%eparam(_, T, true) PS => PS)

    rule #sizeOfEParams(%eparam(_, T, false) PS) => #sizeOfType(T) +Int #sizeOfEParams(PS)
      requires notBool isByteArrayType(T)

    rule #sizeOfEParams(%eparam(_, %bytesT(_), false) PS) => 32 +Int #sizeOfEParams(PS)


    syntax Int  ::= "#sizeOfPackedArgs" "(" TypedLLLExps ")"    [function]
    syntax Int  ::= "#sizeOfPackedArg"  "(" TypedLLLExp  ")"    [function]
 // ----------------------------------------------------------------------
    rule #sizeOfPackedArgs(.TypedLLLExps) => 0

    rule #sizeOfPackedArgs(TLLL TLLLS)    => #sizeOfPackedArg(TLLL) +Int #sizeOfPackedArgs(TLLLS)

    rule #sizeOfPackedArg(@tlll(T, _, _)) => #sizeOfType(T)


    syntax Int  ::= "#sizeOfType" "(" Type ")"     [function]
 // ---------------------------------------------------------
    rule #sizeOfType(T:BaseType) => 32

    //Size #ceil32(L) +Int 32 is sufficient.
    // (The extra 32 bytes are useful when performing conversions/extractions and result have to be padded with 0x00.)
    // Such as slice()/extract32().
    rule #sizeOfType(%bytesT(L)) => #ceil32(L) +Int 64

    rule #sizeOfType(%listT(SUBTYPE, N)) => #sizeOfType(SUBTYPE) *Int N

    rule #sizeOfType(%structT(%annvar(_, T) ANNVARS)) => #sizeOfType(T) +Int #sizeOfType(%structT(ANNVARS))

    rule #sizeOfType(%structT(.AnnVars)) => 0

    rule #sizeOfType(%tupleT(T Ts)) => #sizeOfType(T) +Int #sizeOfType(%tupleT(Ts))

    rule #sizeOfType(%tupleT(.Types)) => 0

    syntax Type  ::= "#getType" "(" TypedLLLExp ")"     [function]
    rule #getType(@tlll(T,_,_)) => T

    syntax KItem  ::= "#canonicalizeType" "(" CType "," Bool /*indexed in event?*/ ")"   [strict(1)]
 // ------------------------------------------------------------------------
    rule #canonicalizeType(%bytesT(_), false) => "bytes"

    rule #canonicalizeType(%bytesT(L),  true) => "bytes" +String Int2String(L)

    rule #canonicalizeType(%listT(SUBTYPE, N), _)
        => #canonicalizeListType(#canonicalizeType(SUBTYPE, false), N)
      requires notBool isByteArrayType(SUBTYPE)

    rule (. => #exception("List of byte arrays not allowed."))
         ~> #canonicalizeType(%listT(SUBTYPE:ByteArrayType, _), _)

    rule #canonicalizeType(%num, _) => "int128"

    rule #canonicalizeType(%unitT(%num, _:Map,_), _) => "int128"

    rule #canonicalizeType(%decimal, _) => "decimal10"

    rule #canonicalizeType(%unitT(%decimal, _:Map,_), _) => "decimal10"

    rule #canonicalizeType(%num256, _) => "uint256"
   
    rule #canonicalizeType(%bool, _) => "bool"
 
    rule #canonicalizeType(_:AddressType, _) => "address"
 
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

    rule #canonicalizeType(%tupleT(Ts), _) => #canonicalizeTupleType(Ts, "", "")

    syntax KItem  ::= "#canonicalizeTupleType" "(" Types "," K "," String ")"   [strict(2)]

    rule #canonicalizeTupleType(T:Type Ts => Ts,
                                S:String => #canonicalizeType(#parseType(T, true), false),
                                SAcc => SAcc +String asString(#if SAcc ==String "" #then "" #else "," #fi) +String S)

    rule #canonicalizeTupleType(.Types, S:String, SAcc)
         => "(" +String SAcc +String asString(#if SAcc ==String "" #then "" #else "," #fi) +String S +String ")"

    syntax String ::= asString ( K )    [function]
    rule asString(S:String) => S

    syntax Int ::= asInt ( K )          [function]
    rule asInt(I:Int) => I

    // Convert from one base type to another. Need to call `#unwrapLoc` first.
    syntax CTypedLLLExp  ::= "#baseTypeConvert"    "(" TypedLLLExp "," Type /*to*/ ")"
    syntax CTypedLLLExp  ::= "#baseTypeConvertAux" "(" TypedLLLExp "," Type        ")"
    syntax CTypedLLLExp  ::= "#baseTypeConvertNoUnit" "(" LLLExp ","  // code
                                                          Type   ","  // from
                                                          Type   ")"  // to
 // ----------------------------------------------------------------------------------
    rule #baseTypeConvert(@tlll(FROMT, CODE, EXPRATTR), TOT)
        => #baseTypeConvertAux(#unwrapLoc(@tlll(FROMT, CODE, EXPRATTR)), TOT)

    rule #baseTypeConvertAux(@tlll(FROMT, CODE, LA), TOT)
        => #ifThenElse(#areUnitsCompatible(FROMT, TOT, #isNumLiteral(CODE)),
                       #baseTypeConvertNoUnit(CODE, #dropUnit(FROMT), #dropUnit(TOT)),
                       #exception("Typecasting unavailable due to incompatible units")
                          ~> #baseTypeConvertAux(@tlll(FROMT, CODE, LA), TOT)
                      )

    rule #baseTypeConvertNoUnit(CODE:LLLExp, FROMT:Type, TOT:Type)
        => #ifThenElse(notBool(isBaseType(FROMT)) orBool notBool(isBaseType(TOT)),
                       #exception("Base type conversion from or to non-base type.")
                          ~> #baseTypeConvertNoUnit(CODE:LLLExp, FROMT:Type, TOT:Type),
             #ifThenElse(FROMT ==K TOT orBool (isAddressType(FROMT) andBool isAddressType(TOT)),
                         @tlll(TOT, CODE, @none),
               #ifThenElse(FROMT ==K %num andBool TOT ==K %decimal,
                           @tlll(TOT, $mul(CODE, @decimalDivisor), @none),
                 #ifThenElse(FROMT ==K %num256 andBool TOT ==K %num,
                             @tlll(TOT, $uclample(CODE, $mload(@maxNumPos)), @none),
                             #exception("Typecasting unavailable.")
                                ~> #baseTypeConvertNoUnit(CODE:LLLExp, FROMT:Type, TOT:Type)))))


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
    rule #parseType(%contractT(CONTRACT:Id), _) => %contractT(CONTRACT)

    rule #parseType(%bytesT(L), _) => %bytesT(L)

    rule #parseType(%listT(SUBTYPE, N), INMEM) => #parseListType(#parseType(SUBTYPE, INMEM), N)

    rule (. => #exception("No mappings allowed for in-memory types, only fixed-size arrays"))
         ~> #parseType(%mapT(KT, VT), true)

    rule #parseType(%mapT(KT, VT), false)
        => #ifThenElse(isBaseType(KT) orBool isByteArrayType(KT),
                       #parseMapType(#parseType(KT, false), #parseType(VT, false)),
                       #exception("Mapping keys must be base or bytes types") ~> #parseType(%mapT(KT, VT), false))

    rule #parseType(%structT(ANNVARS), INMEM) => #parseStructType(ANNVARS, INMEM, .Ids, .AnnVars)

    rule #parseType(%tupleT(Ts), INMEM) => #parseTupleType(Ts, INMEM, .Types)

    // Special Types
    rule #parseType(%timestamp, _)       => %unitT(%num, %sec |-> 1, true)

    rule #parseType(%timedelta, _)       => %unitT(%num, %sec |-> 1, false)

    rule #parseType(%currency_value, _)  => %unitT(%num, %currency |-> 1, false)

    rule #parseType(%currency1_value, _) => %unitT(%num, %currency1 |-> 1, false)

    rule #parseType(%currency2_value, _) => %unitT(%num, %currency2 |-> 1, false)

    rule #parseType(%wei_value, _)       => %unitT(%num, %wei |-> 1, false)

    rule #parseType(%castT(%num, %num256), _) => %num


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
                   #exception("Invalid member variable for struct: " +String Id2String(NAME)))
        ~> #ifThen(#inIds(NAME, NAMES),
                   #exception("Member variable duplicated: " +String Id2String(NAME)))
        ~> #nameWithType(NAME, #parseType(T, INMEM))
        ~> #parseStructType(ANNVARS, INMEM, NAMES, RESULT)

    rule #nameWithType(NAME, T:Type) ~> #parseStructType(ANNVARS, INMEM, NAMES, RESULT)
        => #parseStructType(ANNVARS, INMEM, NAMES ++Id (NAME .Ids), RESULT ++Annvar (%annvar(NAME, T) .AnnVars))


    syntax CType  ::= "#parseTupleType" "(" Types "," Bool "," Types ")"

    rule (. => #parseType(T, INMEM))
         ~> #parseTupleType(T:Type Ts => Ts, INMEM, _)

    rule (T:Type => .)
         ~> #parseTupleType(_, _, FinalTs => FinalTs ++Types T)

    rule #parseTupleType(.Types, _, FinalTs) => %tupleT(FinalTs)

    syntax Types  ::= Types "++Types" Types    [right, function]
 // ---------------------------------------------------------------
    rule (T Ts1) ++Types Ts2        => T (Ts1 ++Types Ts2)

    rule .Types ++Types Ts:Types => Ts


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
    rule #convertToUnitIfPure(T:UnitType, _) => T

    rule #convertToUnitIfPure(%num, @unittuple(UNITMAP, POSITIONAL))
        => %unitT(%num, UNITMAP, POSITIONAL)

    rule #convertToUnitIfPure(%decimal, @unittuple(UNITMAP, POSITIONAL))
        => %unitT(%decimal, UNITMAP, POSITIONAL)

    syntax CTypedLLLExp ::= "#setType" "(" CTypedLLLExp "," Type ")" [strict]
 // -------------------------------------------------------------------------------------------
    rule #changeType(@tlll(T1, CODE, LA), T2) => @tlll(T2, CODE, LA)


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

    rule #areUnitsCompatible(FROM:UnitType, TO, _) => false
      requires notBool(isUnitType(TO))

    rule #areUnitsCompatible(%unitT(_, FROMMAP:Map, FROMPOSITIONAL), %unitT(_, TOMAP:Map, TOPOSITIONAL), _)
        => FROMMAP ==K TOMAP andBool FROMPOSITIONAL ==K TOPOSITIONAL


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

    rule (. => #exception("Cannot insert special character into byte array"))
         ~> #nonEmptystring2Bytes(STR, RESULT)
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


    syntax Int ::= #string2BytesInt( String )       [function]
    syntax Int ::= #string2BytesInt( String , Int ) [function]
 // --------------------------------------------------------------------
    rule #string2BytesInt(S) => #string2BytesInt(S, 0)

    rule #string2BytesInt(S => substrString(S, 1, lengthString(S)),
                          I => I *Int 256 +Int ordChar(substrString(S, 0, 1)))
      requires lengthString(S) >Int 0

    rule #string2BytesInt("", I) => I


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
    rule #computeEventSig(SIG, %eparam(_, T, INDEXED) EPARAMS)
        => #if isCastType(T)
            #then #canonicalizeType(%num256, INDEXED)
            #else #canonicalizeType(#parseType(T, true), INDEXED)
           #fi
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
        => #if isCastType(T)
            #then #canonicalizeType(%num256, false)
            #else #canonicalizeType(#parseType(T, true), false)
           #fi
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
         <env>... %var(NAME) |-> @taddr(T, LOC, LOCATTR) ...</env>

    rule <k> (. => #exception("Undeclared Variable: " +String Id2String(NAME)))
             ~> #lookupVar(%var(NAME)) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in_keys(ENV)

    rule <k> #lookupVar(%svar(NAME)) => @tlll(T, LOC, LOCATTR) ... </k>
         <global>... %svar(NAME) |-> @taddr(T, LOC, LOCATTR) ...</global>

    rule <k> (. => #exception("Persistent variable undeclared: " +String Id2String(NAME)))
             ~> #lookupVar(%svar(NAME)) ...</k>
         <global> GLOBAL </global>
      requires notBool %svar(NAME) in_keys(GLOBAL)

    rule #lookupVar(%subscript(V, EXPR))
        => #lookupVarElement(#lookupVar(V), #compileToVal(EXPR))

    rule #lookupVar(%attribute(V, FIELD:Id))
        => #lookupVarElement(#lookupVar(V), @tlll(%void, FIELD, @none))


    /*  Computes the location for a subscript or attribute expression: base[index] or base.index.
        For attributes, index is of the form @tlll(%void, FIELD, @none)

        source: parser_utils.py - add_variable_offset()
    */
    syntax CTypedLLLExp  ::= "#lookupVarElement" "(" CTypedLLLExp ","  // base
                                                     CTypedLLLExp      // index
                                                 ")"            [seqstrict]
 // ------------------------------------------------------------
    // List
    rule #lookupVarElement(@tlll(%listT(SUBTYPE, N), BASELOC, LOCATTR), INDEXTlll:TypedLLLExp)
        => #lookupListElement(@tlll(%listT(SUBTYPE, N), BASELOC, LOCATTR),
                             #baseTypeConvert(INDEXTlll, %num))

    // Map, index is not byte array
    rule #lookupVarElement(@tlll(%mapT(KT, VT), BASELOC, LOCATTR),
                       @tlll(INDEXT, INDEX, EXPRATTR))
        => #lookupMapElement(@tlll(%mapT(KT, VT), BASELOC, LOCATTR),
                            #baseTypeConvert(@tlll(INDEXT, INDEX, EXPRATTR), KT))
      requires notBool(isByteArrayType(INDEXT))

    // Map, index is byte array
    rule #lookupVarElement(@tlll(%mapT(KT, VT), BASELOC, LOCATTR),
                       @tlll(INDEXT:ByteArrayType, INDEX, EXPRATTR))
        => #lookupMapElement(@tlll(%mapT(KT, VT), BASELOC, LOCATTR),
                            #mapOffsetFromByteArray(@tlll(INDEXT, INDEX, EXPRATTR), KT))

    // Struct
    rule #lookupVarElement(@tlll(%structT(ANNVARS), BASELOC, LOCATTR), @tlll(_, FIELD:Id, _))
        => #lookupStructElement(@tlll(%structT(ANNVARS), BASELOC, LOCATTR),
                                ANNVARS, 0, FIELD)

    // Tuple
    rule #lookupVarElement(@tlll(%tupleT(Ts), BASELOC, LOCATTR), @tlll(_, CNT:Int, _))
         => #lookupTupleElement(@tlll(%tupleT(Ts), BASELOC, LOCATTR), Ts, 0, CNT)


    /* Computes location(List[I]), I converted to %num
    */
    syntax CTypedLLLExp  ::= "#lookupListElement" "(" TypedLLLExp  ","
                                                      CTypedLLLExp ")"  [strict(2)]
    syntax TypedLLLExp  ::= "#lookupListElementAux" "(" TypedLLLExp  ","
                                                        TypedLLLExp  ")"   [function]
 // ------------------------------------------------------------------------------
    rule #lookupListElement(TLLL1:TypedLLLExp, TLLL2:TypedLLLExp)
         => #lookupListElementAux(TLLL1, TLLL2)

    rule #lookupListElementAux(@tlll(%listT(ELEMTYPE, N), BASELOC, @locattr(@storage, MUTABLE)),
                               @tlll(_, INDEX, _))
         => @tlll(ELEMTYPE, $add($sha3_32(BASELOC), $uclamplt(INDEX, N)), @locattr(@storage, MUTABLE))

    rule #lookupListElementAux(@tlll(%listT(SUBTYPE, N), BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                               @tlll(_, INDEX, _))
         => @tlll(SUBTYPE, $add(BASELOC, $uclamplt(INDEX, N)), @locattr(@storage, MUTABLE))

    rule #lookupListElementAux(@tlll(%listT(SUBTYPE, N), BASELOC, @locattr(@memory, MUTABLE)),
                               @tlll(_, INDEX, _))
         => @tlll(SUBTYPE, $add($mul(#sizeOfType(SUBTYPE), $uclamplt(INDEX, N)), BASELOC), @locattr(@memory, MUTABLE))


    syntax CTypedLLLExp  ::= "#lookupMapElement" "(" TypedLLLExp  ","
                                                     CTypedLLLExp ")"  [strict(2)]
 // -----------------------------------------------------------------------------
    rule #lookupMapElement(@tlll(%mapT(KeyT, ValueT), BASELOC, @locattr(@storage, MUTABLE)),
                          @tlll(_, INDEX, _))
        => @tlll(ValueT, $add($sha3_32(BASELOC), INDEX), @locattr(@storage, MUTABLE))

    rule #lookupMapElement(@tlll(%mapT(KT, VT), BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                          @tlll(_, INDEX, _))
        => @tlll(VT, $add(BASELOC, INDEX), @locattr(@storage, MUTABLE))

    rule (. => #exception("Can only have fixed-side arrays in memory, not mappings"))
         ~> #lookupMapElement(@tlll(%mapT(KT, VT), _, @locattr(@memory, _)), _)


    /* Converts a byte array that is used as key in a map to memory offset.

      if not isinstance(typ.keytype, ByteArrayType) or (typ.keytype.maxlen < key.typ.maxlen):
          raise TypeMismatchException('Mapping keys of bytes cannot be cast, use exact same bytes type of: %s',
                                      str(typ.keytype))
      subtype = typ.valuetype
      if len(key.args[0].args) == 3:  # handle bytes literal. Not covering this case
          sub = LLLnode.from_list([
              'seq',
              key,
              ['sha3', ['add', key.args[0].args[-1], 32], ceil32(key.typ.maxlen)]
          ])
      else:
          sub = LLLnode.from_list(['sha3', ['add', key.args[0].value, 32], ['mload', key.args[0].value]])

      fixme possible compiler bug: what if the key is in storage. Then it should be loaded to memory first.
        Tests don't cover this case.
    */
    syntax CTypedLLLExp  ::= "#mapOffsetFromByteArray" "(" TypedLLLExp "," Type ")"
 // -------------------------------------------------------------------------------

    //Case: arg2 not byte array type not covered, should throw exception anyway.
    //Attempt to define a getMaxlen(Type) function (that would help here)
    //  leads to weird exceptions at runtime. K bug probably.
    rule #mapOffsetFromByteArray(@tlll(%bytesT(IMaxLen:Int), INDEX, EXPRATTR), %bytesT(BMaxLen:Int))
        => #ifThenElse(BMaxLen <Int IMaxLen,
              #exception("Mapping keys of bytes cannot be cast, use exact same bytes type of key type")
                ~> #mapOffsetFromByteArray(@tlll(%bytesT(IMaxLen), INDEX, EXPRATTR), %bytesT(BMaxLen)),
              @tlll(%bytes32, $sha3($add(INDEX, 32), $mload(INDEX)), @none)
           )


    syntax CTypedLLLExp  ::= "#lookupStructElement" "(" TypedLLLExp ","  // parent
                                                        AnnVars     ","  // struct fields
                                                        Int         ","  // offset
                                                        Id               // field name
                                                    ")"
 // ------------------------------------------------------------------
    // storage
    rule #lookupStructElement(@tlll(_, BASELOC, @locattr(@storage, MUTABLE)),
                             %annvar(INDEX:Id, FIELDT) ANNVARS, OFFSET:Int,
                             INDEX)
        => @tlll(FIELDT, $add($sha3_32(BASELOC), OFFSET), @locattr(@storage, MUTABLE))


    rule #lookupStructElement(@tlll(BASET, BASELOC, @locattr(@storage, MUTABLE)),
                             %annvar(FIELD:Id, FIELDT:Type) ANNVARS, OFFSET,
                             INDEX:Id)
        => #lookupStructElement(@tlll(BASET, BASELOC, @locattr(@storage, MUTABLE)),
                               ANNVARS, OFFSET +Int 1, INDEX)
      requires INDEX =/=K FIELD

    // storage prehashed
    rule #lookupStructElement(@tlll(_, BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                             %annvar(INDEX:Id, FIELDT) ANNVARS, OFFSET,
                             INDEX)
        => @tlll(FIELDT, $add(BASELOC, OFFSET), @locattr(@storage, MUTABLE))

    rule #lookupStructElement(@tlll(BASET, BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                             %annvar(FIELD:Id, FIELDT) ANNVARS, OFFSET,
                             INDEX:Id)
        => #lookupStructElement(@tlll(BASET, BASELOC, @locattr(@storage_prehashed, MUTABLE)),
                               ANNVARS, OFFSET +Int 1, INDEX)
      requires INDEX =/=K FIELD

    // memory
    rule #lookupStructElement(@tlll(_, BASELOC, @locattr(@memory, MUTABLE)),
                             %annvar(INDEX:Id, FIELDT) ANNVARS, OFFSET,
                             INDEX:Id)
        => @tlll(FIELDT, $add(BASELOC, OFFSET), @locattr(@memory, MUTABLE))

    rule #lookupStructElement(@tlll(_,_, @locattr(@memory, _)),
                             %annvar(FIELD:Id, FIELDT) ANNVARS => ANNVARS,
                             OFFSET => OFFSET +Int #sizeOfType(FIELDT),
                             INDEX:Id)
      requires INDEX =/=K FIELD

    syntax CTypedLLLExp  ::= "#lookupTupleElement" "(" TypedLLLExp ","  // parent
                                                        Types      ","  // tuple types
                                                        Int        ","  // offset
                                                        Int             // index
                                                    ")"

    rule #lookupTupleElement(@tlll(_,_, @locattr(@memory, _)),
                             T:Type Ts => Ts,
                             OFFSET => OFFSET +Int #sizeOfType(T),
                             INDEX:Int => INDEX -Int 1)
      requires INDEX >Int 0

    rule #lookupTupleElement(@tlll(_, BASELOC, @locattr(@memory, MUTABLE)),
                             T:Type _,
                             OFFSET,
                             0)
        => @tlll(T, $add(BASELOC, OFFSET), @locattr(@memory, MUTABLE))

    //defines a new variable of given name in <env>
    syntax CTypedLLLExp  ::= "#newVar" "(" Id "," CType ")"   [strict(2)]
 // ------------------------------------------------------
    rule <k> #newVar(NAME, T:Type) => @tlll(T, LOC, @locattr(@memory, true)) ...</k>
         <env> ENV => ENV[%var(NAME) <- @taddr(T, LOC, @locattr(@memory, true))] </env>
         <nextMem> LOC => LOC +Int #sizeOfType(T) </nextMem>
      requires notBool %var(NAME) in_keys(ENV)

    rule <k> (. => #exception("Duplicate variable name: " +String Id2String(NAME)))
             ~> #newVar(NAME, _) ...</k>
         <env>... %var(NAME) |-> _ ...</env>


    // deletes the variable from <env>
    syntax KItem  ::= "#clearVar" "(" Id ")"
 // -------------------------------------------------
    rule <k> CODE:LLLExps ~> (#clearVar(NAME) => .) ... </k>
         <env>... (%var(NAME) |-> _ => .Map) ...</env>


    syntax CTypedLLLExp  ::= "#lookupOrNewVar" "(" Var "," Type ")"
 // ---------------------------------------------------------------
    rule <k> #lookupOrNewVar(%var(NAME), _) => @tlll(T, LOC, LOCATTR) ... </k>
         <env>... %var(NAME) |-> @taddr(T, LOC, LOCATTR) ...</env>

    rule <k> #lookupOrNewVar(%var(NAME), T) => #newVar(NAME, T) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in_keys(ENV)

    rule #lookupOrNewVar(%svar(NAME), _) => #lookupVar(%svar(NAME))

    rule #lookupOrNewVar(%subscript(V, EXPR), _) => #lookupVar(%subscript(V, EXPR))

    rule #lookupOrNewVar(%attribute(V, FILEDNAME), _) => #lookupVar(%attribute(V, FILEDNAME))


    syntax CTypedLLLExp  ::= "#newLoopVar" "(" Id "," Type ")"
 // ----------------------------------------------------------
    rule <k> (. => #exception("Duplicate iter: " +String Id2String(NAME)))
             ~> #newLoopVar(NAME, T)  ...</k>
         <forvar>... SetItem(NAME) ...</forvar>

    rule <k> #newLoopVar(NAME, T) => #newVar(NAME, T) ... </k>
         <forvar> FORVARS (.Set => SetItem(NAME)) </forvar>
      requires notBool NAME in FORVARS


    // Creates a new variable with unique name, which doesn't need to be removed.
    syntax CTypedLLLExp  ::= "#newPlaceholder" "(" Type ")"
 // -------------------------------------------------------
    rule <k> #newPlaceholder(T)
           => #newVar(String2Id("_placeholder_" +String Int2String(I)), T) ... </k>
         <placeholder> I => I +Int 1 </placeholder>


    // Creates a new variable name. Produces an Id.
    syntax K  ::= "#newVarId"
 // -------------------------------------------------------
    rule <k> #newVarId => String2Id("_var_" +String Int2String(I)) ... </k>
         <placeholder> I => I +Int 1 </placeholder>

// Others
// ======


    //Unwrap expressions of type BaseType into final values. Leave composite types unchanged.
    syntax TypedLLLExp ::= "#unwrapLoc" "(" TypedLLLExp ")"  [function]
 // -------------------------------------------------------------------
    rule #unwrapLoc(@tlll(T:BaseType, CODE, @locattr(@memory, _)))  => @tlll(T, $mload(CODE), @none)

    rule #unwrapLoc(@tlll(T:BaseType, CODE, @locattr(@storage, _))) => @tlll(T, $sload(CODE), @none)

    rule #unwrapLoc(@tlll(T:BaseType, CODE, @none))                 => @tlll(T, CODE, @none)

    rule #unwrapLoc(@tlll(T:Type, CODE, LocAttr))                   => @tlll(T, CODE, LocAttr)
      requires notBool isBaseType(T)


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


    syntax Bool  ::= "#isVarNameValid" "(" Id ")"  [function]
 // ---------------------------------------------------------
    rule #isVarNameValid(NAME) => true
      requires notBool isReservedWord(NAME)

    rule #isVarNameValid(NAME) => false
      requires isReservedWord(NAME)


    syntax CLLLExps  ::= "#mkByteArrayCopier" "(" TypedLLLExp "," TypedLLLExp ")"
    syntax CLLLExps  ::= "#mkByteArrayCopierAux" "(" TypedLLLExp "," TypedLLLExp ")"
 // --------------------------------------------------------------------------------
    rule #mkByteArrayCopier(@tlll(DESTT, DESTCODE, DATTR), @tlll(SOURCET, SOURCECODE, SATTR))
        => #ifThenElse(#getBytesTLen(SOURCET) >Int #getBytesTLen(DESTT),
                       #exception("Cannot cast from greater max-length to shorter max-length.")
                          ~> #mkByteArrayCopier(@tlll(DESTT, DESTCODE, DATTR), @tlll(SOURCET, SOURCECODE, SATTR)),
                       #mkByteArrayCopierAux(@tlll(DESTT, DESTCODE, DATTR),
                                             @tlll(SOURCET, SOURCECODE, SATTR)))

    // memory to memory
    rule #mkByteArrayCopierAux(@tlll(DESTT, DESTCODE, @locattr(@memory, _)),
                               @tlll(SOURCET, SOURCECODE, @locattr(@memory, _)))
        => $with($_source, SOURCECODE,
             $with($_sz/*_pos*/, $add(32, $mload($_source)),
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


    syntax CTypedLLLExp  ::= "#getLength" "(" TypedLLLExp ")"   [function]
 // --------------------------------------------------------
    rule #getLength(@tlll(_, LOC, @locattr(@memory, _))) => @tlll(%num, $mload(LOC), @none)

    rule #getLength(@tlll(_, LOC, @locattr(@storage, _))) => @tlll(%num, $sload($sha3_32(LOC)), @none)

endmodule
