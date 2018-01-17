require "../common/viper-abstract-syntax.k"
require "viper-utils.k"
require "domains.k"

module VIPER-CORE-SEMANTICS
    imports VIPER-ABSTRACT-SYNTAX
    imports VIPER-UTILS
    imports STRING


///////////////////////////////////////////////////////////////////////////////
// Configuration
///////////////////////////////////////////////////////////////////////////////


    configuration
    <T>
      <k> $PGM:Simulation </k>

      <viper>

        <out> .List </out>
        <callStack>     .List </callStack>
        <xStack>        .List </xStack>  // exception stack
        <interimStates> .List </interimStates>

        <memory>   .Map  </memory>
        <memStack> .List </memStack>  // for block scoping
        <forLoop>
          <forvar> .Set  </forvar>  // Variables defined in for loops, eg. for i in range(6):...
          <inLoop> .Set  </inLoop>  // In Loop status. Whether body is currently evaluating within a for-loop or not.
        </forLoop>
        <constant> false </constant>  // Is the current function constant?
        <payable>  false </payable>   // Is the current function payable?
        <return>   %void </return>

        // transaction
        <id>        0 </id>
        <caller>    0 </caller>
        <callValue> 0 </callValue>

        // execution substate
        <substate>
          <selfDestruct> .Set  </selfDestruct>
          <log>          .List </log>
        </substate>

      </viper>

      // Ethereum Network
      // ================

      <network>
        <accounts>
          <account multiplicity="*" type="Bag">
            <acctID>   0   </acctID>
            <balance>  0   </balance>
            <fun>      .Map </fun>
            <event>    .Map </event>
            <external> .Map </external>
            <storage> .Map </storage>
          </account>
        </accounts>
      </network>
    </T>

    syntax Simulation


//////////////////////////////////////////////////////////////////////////////
// Data Types
//////////////////////////////////////////////////////////////////////////////


// Typed Value
// ===========


    syntax TypedValue ::= "@tv" "(" Type "," Value "," Bool ")"  // type, value, literal?

    syntax TypedValues ::= List{TypedValue, ""}  [klabel(TypedValues)]


    syntax TypedValues ::= "#reverseTypedValues" "(" TypedValues "," TypedValues ")"  [function]
 // --------------------------------------------------------------------------------------------
    rule #reverseTypedValues(.TypedValues, RESULT) => RESULT

    rule #reverseTypedValues(TV TVS, RESULT) => #reverseTypedValues(TVS, TV RESULT)


    syntax Value ::= Bool
                   | Int
                   | Decimal
                   | String
                   | Map

    syntax Decimal ::= "@d" "(" Int ")"  // value = acutal_value * @decimalDivisor


// Record
// ======

    syntax ValRecord ::= "@val" "(" TypedValue "," Bool ")"  // typed_value, mutable?

    syntax EventRecord ::= "@event" "(" Id          ","  // event name
                                        EventParams ")"

    syntax FuncRecord ::= "@func" "(" Id     ","  // func name
                                      Params ","
                                      Type   ","  // return type
                                      Stmts  ","  // func body
                                      Bool   ","  // constant ?
                                      Bool   ","  // payable ?
                                      Bool   ","  // private ?
                                      Int    ")"  // order (to prevent recursive call, i.e., a function A can only call other function whose order is less than A)


//////////////////////////////////////////////////////////////////////////////
// Sorts
//////////////////////////////////////////////////////////////////////////////


    // Convention: S{Sort} is a one-one corresponding supersort of Sort. S{Sort}
    //             requires for evaluation (i.e. not KResult).
    syntax SType ::= Type
    syntax SEventParams ::= EventParams
    syntax SParams ::= Params

    syntax KResult ::= TypedValue
                     | TypedValues
                     | Type
                     | EventParams
                     | Params


//////////////////////////////////////////////////////////////////////////////
// Program Loading
//////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#loadCode" "(" Int "," Pgm ")"
 // ------------------------------------------------
    rule <k> #loadCode(ACCTID, %pgm(ES, GS, DEFS))
            => ES ~> GS ~> (DEFS ++Def #mkPublicGetters(GS, .Defs)) ~> #clearState
         ... </k>
         <id> _ => ACCTID </id>


    // TODO: loadCode with init function
    syntax KItem ::= "#loadCodeAndExecInit" "(" Int "," Pgm "," Exprs ")"
 // ---------------------------------------------------------------------


// Event Declarations
// ==================

    rule .Events => .

    rule E:Event ES:Events => E ~> ES

    rule <k> %event(EVENTNAME, EPARAMS)
            => #checkEventParams(EPARAMS, 0, .Ids)
            ~> #addEvent(EVENTNAME,
                         #parseTypeForEventParams(EPARAMS, .EventParams))
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <event> EVENTS </event>
           ...
         </account>
      requires notBool EVENTNAME in_keys(EVENTS)

    rule <k> %event(EVENTNAME, EPARAMS)
            => @exception("Duplicate event name: " +String Id2String(EVENTNAME))
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <event> EVENTS </event>
           ...
         </account>
      requires EVENTNAME in_keys(EVENTS)


    syntax KItem ::= "#checkEventParams" "(" EventParams ","
                                             Int         ","  // # of topics
                                             Ids         ")"  // for checking duplicate names
 // --------------------------------------------------------
    rule #checkEventParams(.EventParams, TOPICNUM, NAMES) => .
      requires TOPICNUM <=Int 3

    rule #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
       => #checkEventParam(%eparam(NAME, T, true), NAMES)
       ~> #checkEventParams(EPARAMS, TOPICNUM +Int 1, NAMES ++Id (NAME .Ids))
      requires TOPICNUM <Int 3

    rule #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
        => #exception("Maximum of 3 topics.")
      requires TOPICNUM >=Int 3

    rule #checkEventParams(%eparam(NAME, T, false) EPARAMS, TOPICNUM, NAMES)
        => #checkEventParam(%eparam(NAME, T, false), NAMES)
        ~> #checkEventParams(EPARAMS, TOPICNUM, NAMES ++Id (NAME .Ids))


    syntax KItem ::= "#checkEventParam" "(" EventParam "," Ids ")"
 // --------------------------------------------------------------
    rule #checkEventParam(%eparam(NAME, T, _), NAMES)
        => #checkEventParamType(T)
        ~> #if notBool #isVarNameValid(NAME)
             #then @exception("Argument name invalid or reserved: " +String Id2String(NAME)) #fi
        ~> #if #isInIds(NAME, NAMES)
             #then @exception("Duplicate function argument name: " +String Id2String(NAME)) #fi


    syntax KItem ::= "#checkEventParamType" "(" Type ")"
 // ----------------------------------------------------
    rule #checkEventParamType(%bytesT(N)) => .
      requires N <=Int 32

    rule #checkEventParamType(%bytesT(N)) => #exception("Can only log a maximum of 32 bytes at a time.")
      requires N >Int 32

    rule #checkEventParamType(T) => .
      requires notBool isByteArrayType(T)


    syntax KItem ::= "#addEvent" "(" Id "," SEventParams ")"  [strict(2)]
 // ---------------------------------------------------------------------
    rule <k> #addEvent(EVENTNAME, EPARAMS) => . ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <event> EVENTS => EVENTS[EVENTNAME <- @event(EVENTNAME, EPARAMS)] </event>
           ...
         </account>


    syntax SEventParams ::= "#parseTypeForEventParams" "(" EventParams "," EventParams ")"
 // --------------------------------------------------------------------------------------
    rule #parseTypeForEventParams(.EventParams, RESULT) => RESULT

    rule #parseTypeForEventParams(%eparam(NAME, T, ISTOPIC) EPARAMS, RESULT)
        => #parseTypeForEventParam(NAME, #parseType(T, true), ISTOPIC)
        ~> #parseTypeForEventParams(EPARAMS, RESULT)

    rule EPARAM:EventParam ~> #parseTypeForEventParams(EPARAMS, RESULT)
        => #parseTypeForEventParams(EPARAMS, RESULT ++Eparam (EPARAM .EventParams))


    syntax KItem ::= "#parseTypeForEventParam" "(" Id "," SType "," Bool ")"  [strict(2)]
 // -------------------------------------------------------------------------------------
    rule #parseTypeForEventParam(NAME, T:Type, ISTOPIC) => %eparam(NAME, T, ISTOPIC)


// Global Declarations
// ===================


    rule .Globals => .

    rule G:Global GS:Globals => G ~> GS

    rule <k> %svdecl(VARNAME, T, _)
            => #if notBool #isVarNameValid(VARNAME)
                #then @exception("Variable name invalid or reserved: " +String Id2String(VARNAME)) #fi
            ~> #addGlobal(VARNAME, #parseType(T, false))
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires notBool VARNAME in_keys(STORAGE)

    rule <k> %svdecl(VARNAME, T, _)
            => @exception("Cannot declare a persistent variable twice! " +String Id2String(VARNAME))
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires VARNAME in_keys(STORAGE)


    syntax KItem ::= "#addGlobal" "(" Id "," SType ")"  [strict(2)]
 // ---------------------------------------------------------------
    rule <k> #addGlobal(VARNAME, T:Type) => . ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE
                    => STORAGE[VARNAME <- @val(#defaultTypedValue(T), true)] </storage>
           ...
         </account>
      requires notBool VARNAME in_keys(STORAGE)


// Function Declarations
// =====================


    rule FUNCDEFS:Defs => #addFuncs(FUNCDEFS, 0)


    syntax KItem ::= "#addFuncs" "(" Defs "," Int /*order*/ ")"
 // -----------------------------------------------------------
    rule #addFuncs(.Defs, _) => .

    rule #addFuncs(%fdecl(DECS, FUNCNAME, PARAMS, T, FUNCBODY) DEFS, ORDER)
        => #addFunc(FUNCNAME, PARAMS, T, FUNCBODY,
                    #isInDecorators(%@constant, DECS),
                    #isInDecorators(%@payable , DECS),
                    #isInDecorators(%@private , DECS),
                    #isInDecorators(%@public  , DECS),
                    ORDER)
        ~> #addFuncs(DEFS, ORDER +Int 1)


    syntax KItem ::= "#addFunc" "(" Id     ","  // func name
                                    Params ","
                                    Type   ","  // return type
                                    Stmts  ","  // func body
                                    Bool   ","  // constant?
                                    Bool   ","  // payable?
                                    Bool   ","  // private?
                                    Bool   ","  // public?
                                    Int    ")"  // order
 // ------------------------------------------
    rule <k> #addFunc(FUNCNAME, PARAMS, T, FUNCBODY, ISCONSTANT, ISPAYABLE, ISPRIVATE, ISPUBLIC, ORDER)
            => #checkFuncParams(PARAMS, .Ids)
            ~> #checkPrivatePublicMECE(ISPRIVATE, ISPUBLIC)
            ~> #addFuncAux(FUNCNAME,
                           #parseTypeForParams(PARAMS, .Params),
                           #parseType(T, true),
                           FUNCBODY,
                           ISCONSTANT, ISPAYABLE, ISPRIVATE, ORDER)
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <fun> FUNCS </fun>
           <event> EVENTS </event>
           ...
         </account>
      requires notBool(FUNCNAME in_keys(FUNCS)) andBool notBool(FUNCNAME in_keys(EVENTS))

    rule <k> #addFunc(FUNCNAME, PARAMS, T, FUNCBODY, ISCONSTANT, ISPAYABLE, ISPRIVATE, ISPUBLIC, ORDER)
            => @exception("Duplicate event or function name: " +String Id2String(FUNCNAME))
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <fun> FUNCS </fun>
           <event> EVENTS </event>
           ...
         </account>
      requires (FUNCNAME in_keys(FUNCS)) orBool (FUNCNAME in_keys(EVENTS))


    syntax KItem ::= "#checkFuncParams" "(" Params "," Ids ")"
 // ----------------------------------------------------------
    rule #checkFuncParams(.Params, NAMES) => .

    rule #checkFuncParams(%param(NAME, T) PARAMS, NAMES)
        => #checkFuncParam(%param(NAME, T), NAMES)
        ~> #checkFuncParams(PARAMS, NAMES ++Id (NAME .Ids))


    syntax KItem ::= "#checkFuncParam" "(" Param "," Ids ")"
 // --------------------------------------------------------
     rule #checkFuncParam(%param(NAME, _), NAMES)
        => #if notBool #isVarNameValid(NAME)
             #then @exception("Argument name invalid or reserved: " +String Id2String(NAME)) #fi
        ~> #if #isInIds(NAME, NAMES)
             #then @exception("Duplicate function argument name: " +String Id2String(NAME)) #fi


    syntax KItem ::= "#checkPrivatePublicMECE" "(" Bool /*private?*/ "," Bool /*public?*/ ")"
 // -----------------------------------------------------------------------------------------
    rule #checkPrivatePublicMECE(ISPRIVATE, ISPUBLIC)
        => #if ISPRIVATE ==K true andBool ISPUBLIC ==K true
             #then @exception("Cannot use public and private decorators on the same function.") #fi
        ~> #if ISPRIVATE ==K false andBool ISPUBLIC ==K false
             #then @exception("Function visibility must be declared (@public or @private).") #fi


    syntax KItem ::= "#addFuncAux" "(" Id      ","  // func name
                                       SParams ","
                                       SType   ","  // return type
                                       Stmts   ","  // func body
                                       Bool    ","  // constant?
                                       Bool    ","  // payable?
                                       Bool    ","  // private?
                                       Int
                                   ")"  [strict(2, 3)]
 // --------------------------------------------------
    rule <k> #addFuncAux(FUNCNAME, PARAMS, T, FUNCBODY, ISCONSTANT, ISPAYABLE, ISPRIVATE, ORDER)
            => . ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <fun> FUNCS
                => FUNCS[FUNCNAME <- @func(FUNCNAME, PARAMS, T, FUNCBODY, ISCONSTANT, ISPAYABLE, ISPRIVATE, ORDER)] </fun>
           ...
         </account>


    syntax SParams ::= "#parseTypeForParams" "(" Params "," Params ")"
 // ------------------------------------------------------------------
    rule #parseTypeForParams(.Params, RESULT) => RESULT

    rule #parseTypeForParams(%param(NAME, T) PARAMS, RESULT)
        => #parseTypeForParam(NAME, #parseType(T, true))
        ~> #parseTypeForParams(PARAMS, RESULT)

    rule PARAM:Param ~> #parseTypeForParams(PARAMS, RESULT)
        => #parseTypeForParams(PARAMS, RESULT ++Param (PARAM .Params))


    syntax KItem   ::= "#parseTypeForParam"  "(" Id "," SType  ")"  [strict(2)]
 // ---------------------------------------------------------------------------
    rule #parseTypeForParam(NAME, T:Type) => %param(NAME, T)


//////////////////////////////////////////////////////////////////////////////
// Statements
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Expressions
//////////////////////////////////////////////////////////////////////////////


    syntax KItem /*TypedValue*/ ::= "#evalExpr" "(" Expr ")"
 // --------------------------------------------------------


    syntax KItem /*TypedValues*/ ::= "#evalExprs" "(" Exprs "," TypedValues ")"
 // ---------------------------------------------------------------------------
    rule #evalExprs(.Exprs, RESULT) => #reverseTypedValues(RESULT, .TypedValues)

    rule #evalExprs((ARG:Expr ARGS:Exprs), RESULT) => #evalExpr(ARG) ~> #evalExprs(ARGS, RESULT)

    rule ARG:TypedValue ~> #evalExprs(ARGS:Exprs, RESULT) => #evalExprs(ARGS, ARG RESULT)


// Constants
// =========


    rule #evalExpr(I:Int) => @tv(%num, I, true)

    rule #evalExpr(%hex(STR:String)) => @tv(%address, #parseHexWord(STR), true)


// External Call
// =============


    syntax KItem ::= "#ecall" "(" K /*TypedValue*/ "," Id "," K /*TypedValues*/ ")"  [seqstrict(1, 3)]
 // --------------------------------------------------------------------------------------------------
    rule #evalExpr(%ecall(ADDR, FUNCNAME, EXPRS)) => #ecall(#evalExpr(ADDR), FUNCNAME, #evalExprs(EXPRS, .TypedValues))

    rule <k> #ecall(@tv(%address, ACCTID, _), FUNCNAME, TARGS:TypedValues)
            => #push


//////////////////////////////////////////////////////////////////////////////
// Clear State
//////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////////
// Types
///////////////////////////////////////////////////////////////////////////////


// Default Values
// ==============

    syntax TypedValue ::= "#defaultTypedValue" "(" Type ")"  [function]
 // -------------------------------------------------------------------
    rule #defaultTypedValue(%bool) => @tv(%bool, false, false)

    rule #defaultTypedValue(%num) => @tv(%num, 0, false)

    rule #defaultTypedValue(%decimal) => @tv(%decimal, @d(0), false)

    rule #defaultTypedValue(%unitT(%num, UNIT:Map, POSITIONAL)) => @tv(%unitT(%num, UNIT, POSITIONAL), 0, false)

    rule #defaultTypedValue(%unitT(%decimal, UNIT:Map, POSITIONAL)) => @tv(%unitT(%decimal, UNIT, POSITIONAL), @d(0), false)

    rule #defaultTypedValue(%num256) => @tv(%num256, 0, false)

    rule #defaultTypedValue(%signed256) => @tv(%signed256, 0, false)

    rule #defaultTypedValue(%bytes32) => @tv(%bytes32, 0, false)

    rule #defaultTypedValue(%address) => @tv(%address, 0, false)

    rule #defaultTypedValue(%bytesT(N)) => @tv(%bytesT(N), "", false)

    rule #defaultTypedValue(%listT(SUBTYPE, LEN)) => @tv(%listT(SUBTYPE, LEN), #defaultValueListType(SUBTYPE, LEN, 0), false)

    rule #defaultTypedValue(%mapT(KT, VT)) => @tv(%mapT(KT, VT), .Map, false)

    rule #defaultTypedValue(%structT(ANNVARS)) => @tv(%structT(ANNVARS), #defaultValueStructType(ANNVARS), false)


    syntax Map ::= "#defaultValueListType" "(" Type "," Int "," Int ")"  [function]
 // -------------------------------------------------------------------------------
    rule #defaultValueListType(SUBTYPE, N, N) => .Map

    rule #defaultValueListType(T, N, INDEX)
        => (INDEX |-> #defaultTypedValue(T)) #defaultValueListType(T, N, INDEX +Int 1)
      requires INDEX <Int N


    syntax Map ::= "#defaultValueStructType" "(" AnnVars ")"  [function]
 // --------------------------------------------------------------------
    rule #defaultValueStructType(.AnnVars) => .Map

    rule #defaultValueStructType(%annvar(FIELDNAME, FIELDTYPE) ANNVARS)
        => (FIELDNAME |-> #defaultTypedValue(FIELDTYPE)) #defaultValueStructType(ANNVARS)


// Type Parsing
// ============


    syntax SType ::= "#parseType" "(" Type "," Bool /*in memory?*/ ")"
 // ------------------------------------------------------------------
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

    rule #parseType(%bytesT(N), _)
        => #if N <=Int 0
             #then @exception("Bad byte array length: " +String Int2String(N)) #fi
        ~> %bytesT(N)

    rule #parseType(%listT(SUBTYPE, N), INMEMORY)
        => #parseListType(#parseType(SUBTYPE, INMEMORY), N)

    rule #parseType(%mapT(KT, VT), true)
        => @exception("No mappings allowed for in-memory types, only fixed-size arrays")

    rule #parseType(%mapT(KT, VT), false)
        => #if isBaseType(KT) orBool isByteArrayType(KT)
             #then #parseMapType(#parseType(KT, false), #parseType(VT, false))
             #else @exception("Mapping keys must be base or bytes types") #fi

    rule #parseType(%structT(ANNVARS), INMEMORY)
        => #parseStructType(ANNVARS, INMEMORY, .Ids, .AnnVars)

    // TODO: support Tuple

    // Special Types
    rule #parseType(%timestamp, _)       => %unitT(%num, %sec |-> 1, true)

    rule #parseType(%timedelta, _)       => %unitT(%num, %sec |-> 1, false)

    rule #parseType(%currency_value, _)  => %unitT(%num, %currency |-> 1, false)

    rule #parseType(%currency1_value, _) => %unitT(%num, %currency1 |-> 1, false)

    rule #parseType(%currency2_value, _) => %unitT(%num, %currency2 |-> 1, false)

    rule #parseType(%wei_value, _)       => %unitT(%num, %wei |-> 1, false)


    syntax SType  ::= "#parseListType" "(" SType "," Int ")"  [strict(1)]
 // ---------------------------------------------------------------------
    rule #parseListType(T, N) => %listT(T, N)


    syntax SType  ::= "#parseMapType" "(" SType "," SType ")"  [seqstrict]
 // ----------------------------------------------------------------------
    rule #parseMapType(KT, VT) => %mapT(KT, VT)


    syntax SType  ::= "#parseStructType" "(" AnnVars "," Bool "," Ids "," AnnVars ")"
    syntax KItem  ::= "@typedName" "(" Id "," SType ")"  [strict(2)]
 // ---------------------------------------------------------------------------------
    rule #parseStructType(.AnnVars, _, _, ANNVARS) => %structT(ANNVARS)

    rule #parseStructType(%annvar(NAME, T) ANNVARS, INMEMORY, NAMES, RESULT)
        => #if notBool #isVarNameValid(NAME)
             #then @exception("Invalid member variable for struct.") #fi
        ~> #if #isInIds(NAME, NAMES)
             #then @exception("Member variable duplicated: " +String Id2String(NAME)) #fi
        ~> @typedName(NAME, #parseType(T, INMEMORY))
        ~> #parseStructType(ANNVARS, INMEMORY, NAMES, RESULT)

    rule @typedName(NAME, T:Type) ~> #parseStructType(ANNVARS, INMEM, NAMES, RESULT)
        => #parseStructType(ANNVARS, INMEM, NAMES ++Id (NAME .Ids), RESULT ++Annvar (%annvar(NAME, T) .AnnVars))


// Units
// =====


    syntax UnitType ::= "%unitT" "(" PureNumType "," Map "," Bool /*positional*/ ")"  // internal representation of unit type


    syntax SType ::= "#parseUnitType" "(" UnitType ")"
 // --------------------------------------------------



endmodule
