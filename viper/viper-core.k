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
        <return>        %void </return>

        <global>   .Map  </global>
        <env>      .Map  </env>
        <envStack> .List </envStack>  // for block scoping
        <forLoop>
          <forvar> .Set  </forvar>  // Variables defined in for loops, eg. for i in range(6):...
          <inLoop> .Set  </inLoop>  // In Loop status. Whether body is currently evaluating within a for-loop or not.
        </forLoop>
        <fun>      .Map </fun>
        <event>    .Map </event>
        <external> .Map </external>

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
            <code>
              <funDef>      .Map </funDef>
              <eventSig>    .Map </eventSig>
              <externalSig> .Map </externalSig>
            </code>
            <storage> .Map </storage>
          </account>
        </accounts>
      </network>
    </T>

    syntax Simulation


//////////////////////////////////////////////////////////////////////////////
// Data Types
//////////////////////////////////////////////////////////////////////////////


    syntax EventRecord ::= "@event" "(" Int         ","  // event_id
                                        Id          ","  // name
                                        EventParams ")"


    syntax ValRecord ::= "@val" "(" TypedValue "," Bool ")"  // typed_value, mutable?

    syntax TypedValue ::= "@tv" "(" Type "," Value "," Bool ")"  // type, value, literal?

    syntax Value ::= Int
                   | Decimal
                   | Map
                   | UndefinedValue

    syntax UndefinedValue ::= "undef"

    syntax Decimal ::= "@d" "(" Int ")"  // value = acutal_value * @decimalDivisor


//////////////////////////////////////////////////////////////////////////////
// Sorts
//////////////////////////////////////////////////////////////////////////////


    // Convention: S{Sort} is a one-one corresponding supersort of Sort. S{Sort}
    //             requires for evaluation (i.e. not KResult).
    syntax SType ::= Type
    syntax SEventParams ::= EventParams

    syntax KResult ::= Int | String
                     | TypedValue
                     | Type
                     | EventParams


//////////////////////////////////////////////////////////////////////////////
// Program Loading
//////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#loadCode" "(" Pgm "," Exprs ")"
 // --------------------------------------------------
    rule #loadCode(%pgm(ES, GS, DEFS), _) => ES ~> GS ~> DEFS


// Event Declarations
// ==================

    rule .Events => .

    rule E:Event ES:Events => E ~> ES

    rule <k> %event(EVENTNAME, EPARAMS)
            => #checkEventParams(EPARAMS, 0, .Ids)
            ~> #addEvent(#computeEventId(EVENTNAME, EPARAMS),
                         EVENTNAME,
                         #parseTypeForEventParams(EPARAMS, .EventParams))
         ... </k>
         <event> EVENTS </event>
      requires notBool EVENTNAME in_keys(EVENTS)

    rule <k> %event(EVENTNAME, EPARAMS)
            => @exception("Duplicate event name: " +String Id2String(EVENTNAME))
         ... </k>
         <event> EVENTS </event>
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
    rule #checkEventParamType(%bytesT(L)) => .
      requires L <=Int 32

    rule #checkEventParamType(%bytesT(L)) => #exception("Can only log a maximum of 32 bytes at a time.")
      requires L >Int 32

    rule #checkEventParamType(T) => .
      requires notBool isByteArrayType(T)


    syntax KItem ::= "#addEvent" "(" K "," Id "," SEventParams ")"  [seqstrict(1, 3)]
 // ---------------------------------------------------------------------------------
    rule <k> #addEvent(EID:Int, EVENTNAME, EPARAMS) => . ... </k>
         <event> EVENTS => EVENTS[EVENTNAME <- @event(EID, EVENTNAME, EPARAMS)] </event>


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
    rule #parseTypeForEventParam(NAME, T:Type, TOPIC) => %eparam(NAME, T, TOPIC)


// Global Declarations
// ===================


    rule .Globals => .

    rule G:Global GS:Globals => G ~> GS

    rule <k> %svdecl(VARNAME, T, _)
            => #if notBool #isVarNameValid(VARNAME)
                #then @exception("Variable name invalid or reserved: " +String Id2String(VARNAME)) #fi
            ~> #addGlobal(VARNAME, #parseType(T, false))
         ... </k>
         <global> GLOBALS </global>
      requires notBool VARNAME in_keys(GLOBALS)

    rule <k> %svdecl(VARNAME, T, _)
            => @exception("Cannot declare a persistent variable twice! " +String Id2String(VARNAME))
         ... </k>
         <global> GLOBALS </global>
      requires VARNAME in_keys(GLOBALS)


    syntax KItem ::= "#addGlobal" "(" Id "," SType ")"  [strict(2)]
 // ---------------------------------------------------------------
    rule <k> #addGlobal(VARNAME, T:Type) => . ... </k>
         <global> GLOBALS
                 => GLOBALS[VARNAME <- @val(@tv(T, #initialize(T), false), true)] </global>
      requires notBool VARNAME in_keys(GLOBALS)



//////////////////////////////////////////////////////////////////////////////
// Statements
//////////////////////////////////////////////////////////////////////////////


    syntax Value ::= "#initialize" "(" Type ")"  [function]
 // -------------------------------------------------------
    rule #initialize(%bool) => false

    rule #initialize(%num) => 0

    rule #initialize(%decimal) => @d(0)

    rule #initialize(%unitT(%num, _:Map, _)) => 0

    rule #initialize(%unitT(%decimal, _:Map, _)) => @d(0)

    rule #initialize(%num256) => 0

    rule #initialize(%signed256) => 0

    rule #initialize(%bytes32) => 0

    rule #initialize(%address) => 0

    rule #initialize(%bytesT(L)) => ""

    rule #initialize(%listT(T, N)) => #initializeList(T, N, 0)

    rule #initialize(%mapT(KT, VT)) => .Map

    rule #initialize(%structT(ANNVARS)) => #initializeStruct(ANNVARS)


    syntax Map ::= "#initializeList" "(" Type "," Int "," Int ")"  [function]
 // -------------------------------------------------------------------------
    rule #initializeList(T, N, N) => .Map

    rule #initializeList(T, N, INDEX)
        => (INDEX |-> #initialize(T)) #initializeList(T, N, INDEX +Int 1)


    syntax Map ::= "#initializeStruct" "(" AnnVars ")"  [function]
 // --------------------------------------------------------------
    rule #initializeStruct(.AnnVars) => .Map

    rule #initializeStruct(%annvar(FIELDNAME, FIELDTYPE) ANNVARS)
        => (FIELDNAME |-> #initialize(FIELDTYPE)) #initializeStruct(ANNVARS)


//////////////////////////////////////////////////////////////////////////////
// Exception
//////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "@exception" "(" String ")"
 // -------------------------------------------


///////////////////////////////////////////////////////////////////////////////
// Types
///////////////////////////////////////////////////////////////////////////////


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

    rule #parseType(%bytesT(L), _)
        => #if L <=Int 0
             #then @exception("Bad byte array length: " +String Int2String(L)) #fi
        ~> %bytesT(L)

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
