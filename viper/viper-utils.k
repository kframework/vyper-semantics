require "../common/viper-abstract-syntax.k"

module VIPER-UTILS
    imports VIPER-ABSTRACT-SYNTAX
    imports KRYPTO


///////////////////////////////////////////////////////////////////////////////
// Constants
///////////////////////////////////////////////////////////////////////////////


    syntax Int ::= "pow160"           [function]
                 | "@decimalDivisor"  [function]
                 | "@maxNum"          [function]
                 | "@minNum"          [function]
                 | "@maxDecimal"      [function]
                 | "@minDecimal"      [function]
                 | "@maxNum256"       [function]
 // --------------------------------------------
    rule pow160 => 2 ^Int 160

    rule @decimalDivisor => 10000000000

    rule @maxNum     => 2 ^Int 127 -Int 1

    rule @minNum     => -2 ^Int 127

    rule @maxDecimal => (2 ^Int 127 -Int 1) *Int @decimalDivisor

    rule @minDecimal => (-2 ^Int 127) *Int @decimalDivisor

    rule @maxNum256  => 2 ^Int 256 -Int 1


///////////////////////////////////////////////////////////////////////////////
// Address
///////////////////////////////////////////////////////////////////////////////


    syntax Int ::= "#addr" "(" Int ")"  [function]
 // ----------------------------------------------
    rule #addr(W) => W modInt pow160


    syntax Int ::= "#parseAddr" "(" String ")"  [function]
 // ------------------------------------------------------
    rule #parseAddr(S) => #addr(#parseHexWord(S))


///////////////////////////////////////////////////////////////////////////////
// #if _ #then _ #else _ #fi
///////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#if" Bool "#then" K "#fi"
                   | "#if" Bool "#then" K "#else" K "#fi"
 // -----------------------------------------------------
    rule #if true  #then THENCLAUSE #fi => THENCLAUSE

    rule #if false #then THENCLAUSE #fi => .

    rule #if true  #then THENCLAUSE #else ELSECLAUSE #fi => THENCLAUSE

    rule #if false #then THENCLAUSE #else ELSECLAUSE #fi => ELSECLAUSE


///////////////////////////////////////////////////////////////////////////////
// Helper functions
///////////////////////////////////////////////////////////////////////////////


    syntax Int ::= #parseHexWord ( String ) [function]
                 | #parseWord    ( String ) [function]
 // --------------------------------------------------
    rule #parseHexWord("")   => 0

    rule #parseHexWord("0x") => 0

    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16)
      requires (S =/=String "") andBool (S =/=String "0x")

    rule #parseWord("") => 0

    rule #parseWord(S)  => #parseHexWord(S)
      requires lengthString(S) >=Int 2 andBool substrString(S, 0, 2) ==String "0x"

    rule #parseWord(S)  => String2Int(S)  [owise]


    // TODO: Add more invalid cases(utils.py)
    syntax Bool ::= "#isVarNameValid" "(" Id ")"  [function]
 // --------------------------------------------------------
    rule #isVarNameValid(NAME) => true
      requires notBool #isReservedWords(Id2String(NAME))

    rule #isVarNameValid(NAME) => false
      requires #isReservedWords(Id2String(NAME))


    syntax Bool ::= "#isReservedWords" "(" String ")"  [function]
 // -------------------------------------------------------------
    rule #isReservedWords(STR)
        =>       (STR ==K "int128") orBool (STR ==K "int256") orBool (STR ==K "uint256")
          orBool (STR ==K "address") orBool (STR ==K "bytes32") orBool (STR ==K "real")
          orBool (STR ==K "real128x128")
          /* language constructor */
          orBool (STR ==K "for") orBool (STR ==K "break") orBool (STR ==K "continue")
          orBool (STR ==K "def") orBool (STR ==K "assert") orBool (STR ==K "throw")
          orBool (STR ==K "__init__") orBool (STR ==K "true") orBool (STR ==K "false")
          orBool (STR ==K "self") orBool (STR ==K "this") orBool (STR ==K "pass")
          /* unit */
          orBool (STR ==K "ether") orBool (STR ==K "wei") orBool (STR ==K "gwei")
          orBool (STR ==K "kwei") orBool (STR ==K "mei") orBool (STR ==K "twei")
          orBool (STR ==K "pwei") orBool (STR ==K "finny") orBool (STR ==K "szabo")
          orBool (STR ==K "shannon") orBool (STR ==K "lovelace") orBool (STR ==K "ada")
          orBool (STR ==K "babbage")


// Compute signatures
// ==================


    // event id
    syntax KItem /*Int*/ ::= "#computeEventId"    "(" Id "," EventParams ")"
    syntax KItem /*Int*/ ::= "#computeEventIdAux" "(" K ")"  [strict]
 // ------------------------------------------------------------------------
    rule #computeEventId(EVENTNAME, EPARAMS)
        => #computeEventIdAux(#computeEventSig(Id2String(EVENTNAME) +String "(", EPARAMS))

    rule #computeEventIdAux(EVENTSIG:String)
        => String2Base(Keccak256(EVENTSIG), 16)


    syntax KItem /*String*/ ::= "#computeEventSig"    "(" String "," EventParams ")"
    syntax KItem /*String*/ ::= "#computeEventSigAux" "(" String "," EventParams ")"
 // --------------------------------------------------------------------------------
    rule #computeEventSig(SIG, %eparam(_, T, _) EPARAMS)
        => #canonicalizeType(T, true)
        ~> #computeEventSigAux(SIG, EPARAMS)

    rule TYPE:String ~> #computeEventSigAux(SIG, EPARAM1 EPARAMS)
        => #computeEventSig(SIG +String TYPE +String ",", EPARAM1 EPARAMS)

    rule TYPE:String ~> #computeEventSigAux(SIG, .EventParams)
        => #computeEventSig(SIG +String TYPE, .EventParams)

    rule #computeEventSig(SIG, .EventParams) => SIG +String ")"


    // func id
    syntax KItem /*Int*/ ::= "#computeFuncId"    "(" Id "," Params ")"
    syntax KItem /*Int*/ ::= "#computeFuncIdAux" "(" K ")"  [strict]
 // ------------------------------------------------------------------
    rule #computeFuncId(FUNCNAME, PARAMS)
        => #computeFuncIdAux(#computeFuncSig(Id2String(FUNCNAME) +String "(", PARAMS))

    rule #computeFuncIdAux(FUNCSIG:String)
        => String2Base(substrString(Keccak256(FUNCSIG), 0, 8), 16)


    syntax KItem /*String*/ ::= "#computeFuncSig"    "(" String "," Params ")"
    syntax KItem /*String*/ ::= "#computeFuncSigAux" "(" String "," Params ")"
 // ----------------------------------------------------------------
    rule #computeFuncSig(SIG, %param(_,T) PARAMS)
        => #canonicalizeType(T, false)
        ~> #computeFuncSigAux(SIG, PARAMS)

    rule TYPE:String ~> #computeFuncSigAux(SIG, PARAM1 PARAMS)
        => #computeFuncSig(SIG +String TYPE +String ",", PARAM1 PARAMS)

    rule TYPE:String ~> #computeFuncSigAux(SIG, .Params)
        => #computeFuncSig(SIG +String TYPE, .Params)

    rule #computeFuncSig(SIG, .Params) => SIG +String ")"


// Make public getters
// ===================


    syntax Defs ::= "#mkPublicGetters" "(" Globals "," Defs /*result*/ ")"  [function]
 // ----------------------------------------------------------------------------------
    rule #mkPublicGetters(.Globals, RESULTDEFS) => RESULTDEFS

    rule #mkPublicGetters(%svdecl(VARNAME, T, %public) GS, RESULTDEFS)
        => #mkPublicGetters(GS,
                            RESULTDEFS ++Def #mkPublicGetter(Id2String(VARNAME), .Params, T, %svar(VARNAME), 0))

    rule #mkPublicGetters(%svdecl(_, _, %private) GS, RESULTDEFS)
        => #mkPublicGetters(GS, RESULTDEFS)


    // Struct type and Map will generate multiple getter functions
    syntax Defs ::= "#mkPublicGetter" "(" String ","  // getter function name
                                          Params ","  // getter function params
                                          Type   ","  // getter function return type (if it is base type)
                                          Var    ","  // return variable
                                          Int         // depth
                                      ")"  [function]
 // -------------------------------------------------
    // Base Type
    rule #mkPublicGetter(VARNAME, PARAMS, T:BaseType, VAR, DEPTH)
        => %fdecl(%@public %@constant .Decorators,
                  String2Id("get_" +String VARNAME),
                  PARAMS,
                  T,
                  %return(VAR) .Stmts) .Defs

    // Byte Array
    rule #mkPublicGetter(VARNAME, PARAMS, %bytesT(N), VAR, DEPTH)
        => %fdecl(%@public %@constant .Decorators,
                  String2Id("get_" +String VARNAME),
                  PARAMS,
                  %bytesT(N),
                  %return(VAR) .Stmts) .Defs

    // List
    rule #mkPublicGetter(VARNAME, PARAMS, %listT(SUBTYPE, N), VAR, DEPTH)
        => #mkPublicGetter(VARNAME,
                           PARAMS ++Param (%param(String2Id("arg" +String Int2String(DEPTH)), %num) .Params),
                           SUBTYPE,
                           %subscript(VAR, %var(String2Id("arg" +String Int2String(DEPTH)))),
                           DEPTH +Int 1)

    // Map
    rule #mkPublicGetter(VARNAME, PARAMS, %mapT(KT, VT), VAR, DEPTH)
        => #mkPublicGetter(VARNAME,
                           PARAMS ++Param (%param(String2Id("arg" +String Int2String(DEPTH)), KT) .Params),
                           VT,
                           %subscript(VAR, %var(String2Id("arg" +String Int2String(DEPTH)))),
                           DEPTH +Int 1)

    // Struct
    rule #mkPublicGetter(VARNAME, PARAMS, %structT(%annvar(FIELDNAME, FIELDTYPE) ANNVARS), VAR, DEPTH)
        => #mkPublicGetter(VARNAME +String "__" +String Id2String(FIELDNAME),
                           PARAMS,
                           FIELDTYPE,
                           %attribute(VAR, FIELDNAME),
                           DEPTH)
           ++Def #mkPublicGetter(VARNAME, PARAMS, %structT(ANNVARS), VAR, DEPTH)

    rule #mkPublicGetter(VARNAME, PARAMS, %structT(.AnnVars), VAR, DEPTH)
        => .Defs


///////////////////////////////////////////////////////////////////////////////
// Types
///////////////////////////////////////////////////////////////////////////////


    syntax KItem /*String*/ ::= "#canonicalizeType" "(" Type "," Bool /*event?*/ ")"
 // --------------------------------------------------------------------------------
    rule #canonicalizeType(%bytesT(N), EVENT)
        => #if EVENT ==K true andBool N <=Int 32
             #then "bytes" +String Int2String(N)
             #else "bytes"
           #fi

    rule #canonicalizeType(%listT(SUBTYPE, N), _)
        => #canonicalizeListType(#canonicalizeType(SUBTYPE, false), N)
      requires isBaseType(SUBTYPE) orBool isListType(SUBTYPE)

    rule #canonicalizeType(%listT(SUBTYPE, N), _)
        => @staticException("List of byte arrays not allowed.")
      requires isByteArrayType(SUBTYPE)

    rule #canonicalizeType(%num, _) => "int128"

    rule #canonicalizeType(%unitT(%num, _:Unit, _), _) => "int128"

    rule #canonicalizeType(%decimal, _) => "decimal10"

    rule #canonicalizeType(%unitT(%decimal, _:Unit, _), _) => "decimal10"

    rule #canonicalizeType(%num256, _) => "uint256"

    rule #canonicalizeType(%bool, _) => "bool"

    rule #canonicalizeType(%address, _) => "address"

    rule #canonicalizeType(%bytes32, _) => "bytes32"


    syntax KItem /*String*/ ::= "#canonicalizeListType" "(" K "," Int ")"  [strict(1)]
 // ----------------------------------------------------------------------------------
    rule #canonicalizeListType(T:String, N)
        => T +String "[" +String Int2String(N) +String "]"


///////////////////////////////////////////////////////////////////////////////
// Lists
///////////////////////////////////////////////////////////////////////////////


// Is In List
// ==========


    syntax Bool  ::= "#isInIds" "(" Id "," Ids ")"  [function]
 // ----------------------------------------------------------
    rule #isInIds(ID, .Ids)    => false

    rule #isInIds(ID, ID1 IDS) => true               requires ID ==K ID1

    rule #isInIds(ID, ID1 IDS) => #isInIds(ID, IDS)  requires ID =/=K ID1


    syntax Bool  ::= "#isInDecorators" "(" Decorator "," Decorators ")"  [function]
 // -------------------------------------------------------------------------------
    rule #isInDecorators(DEC, .Decorators) => false

    rule #isInDecorators(DEC, DEC1 DECS) => true                        requires DEC ==K DEC1

    rule #isInDecorators(DEC, DEC1 DECS) => #isInDecorators(DEC, DECS)  requires DEC =/=K DEC1


// List Operation
// ==============

    // TODO: use `reverse` list twice instead of appending to list
    syntax Ids ::= List{Id, ""}
    syntax Ids ::= Ids "++Id" Ids  [right, function]
 // ------------------------------------------------


    syntax AnnVars ::= "#revAnnVars" "(" AnnVars "," AnnVars ")"  [function]
 // ------------------------------------------------------------------------
    rule #revAnnVars(.AnnVars, RESULT) => RESULT

    rule #revAnnVars(ANNVAR ANNVARS, RESULT) => #revAnnVars(ANNVARS, ANNVAR RESULT)


    syntax EventParams ::= "#revEventParams" "(" EventParams "," EventParams ")"  [function]
 // ----------------------------------------------------------------------------------------
    rule #revEventParams(.EventParams, RESULT) => RESULT

    rule #revEventParams(EPARAM EPARAMS, RESULT) => #revEventParams(EPARAMS, EPARAM RESULT)


    syntax Params ::= "#revParams" "(" Params "," Params ")"  [function]
 // -------------------------------------------------------------------
    rule #revParams(.Params, RESULT) => RESULT

    rule #revParams(PARAM PARAMS, RESULT) => #revParams(PARAMS, PARAM RESULT)


    syntax Params ::= Params "++Param" Params  [right, function]
 // ------------------------------------------------------------
    rule .Params ++Param PARAMS:Params => PARAMS

    rule (PARAM PARAMS1) ++Param PARAMS2 => PARAM (PARAMS1 ++Param PARAMS2)


    syntax Defs ::= Defs "++Def" Defs  [right, function]
 // ----------------------------------------------------
    rule .Defs ++Def DEFS:Defs => DEFS

    rule (DEF DEFS1) ++Def DEFS2 => DEF (DEFS1 ++Def DEFS2)


//////////////////////////////////////////////////////////////////////////////
// Exception
//////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "@staticException" "(" String ")"
 // --------------------------------------------------


    syntax KItem ::= "@dynamicException" "(" String ")"
 // ---------------------------------------------------


endmodule
