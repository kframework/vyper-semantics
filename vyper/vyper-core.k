require "../common/vyper-abstract-syntax.k"
require "vyper-utils.k"
require "domains.k"

module VYPER-CORE-SEMANTICS
    imports VYPER-ABSTRACT-SYNTAX
    imports VYPER-UTILS
    imports STRING


///////////////////////////////////////////////////////////////////////////////
// Configuration
///////////////////////////////////////////////////////////////////////////////


    configuration
    <T>
      <k> $PGM:Simulation </k>

      <vyper>

        <callStack>     .List </callStack>
        <interimStates> .List </interimStates>
        <substateStack> .List </substateStack>

        <memory>   .Map  </memory>
        <memStack> .List </memStack>  // for block scoping
        <forLoop>
          <forvar> .Set  </forvar>  // Variables defined in for loops, eg. for i in range(6):...
          <inLoop> .Set  </inLoop>  // In Loop status. Whether body is currently evaluating within a for-loop or not.
        </forLoop>
        <constant> false </constant>  // Is the current function constant?
        <return>   %void </return>
        <order>    -1     </order>  // init value is -1 so that it can call any function in the contract.

        // transaction
        <id>        0 </id>
        <caller>    0 </caller>
        <callValue> 0 </callValue>

        // execution substate
        <substate>
          <selfDestruct> .Set  </selfDestruct>
          <log>          .List </log>
        </substate>

      </vyper>

      // Ethereum Network
      // ================

      <network>
        <activeAccounts> .Set </activeAccounts>
        <accounts>
          <account multiplicity="*" type="Bag">
            <acctID>   0    </acctID>
            <balance>  0    </balance>
            <fun>      .Map </fun>
            <event>    .Map </event>
            <external> .Map </external>
            <storage>  .Map </storage>
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


    syntax TypedValue ::= "@tv" "(" Type "," Value ")"  // type, value

    syntax Value ::= Bool
                   | Int
                   | Decimal
                   | String
                   | Map

    syntax Decimal ::= "@d" "(" Int ")"  // value = acutal_value * @decimalDivisor


// Evaled Var
// ==========

   // Var with Expr inside evaluated.
   syntax EvaledVar ::= "@%var"  "(" Id ")"
                      | "@%svar" "(" Id ")"
                      | "@%subscript" "(" EvaledVar "," EvaledExpr ")"
                      | "@%attribute" "(" EvaledVar "," Id ")"


// Evaluated Expression
// ====================


    syntax EvaledExpr  ::= "@ee" "(" Type "," Value "," Bool ")"  // type, value, literal?


    syntax EvaledExprs ::= List{EvaledExpr, ""}  [klabel(EvaledExprs)]


    syntax EvaledExprs ::= "#revEvaledExprs" "(" EvaledExprs "," EvaledExprs ")"  [function]
 // ----------------------------------------------------------------------------------------
    rule #revEvaledExprs(.EvaledExprs, RESULT) => RESULT

    rule #revEvaledExprs(EEXPR EEXPRS, RESULT) => #revEvaledExprs(EEXPRS, EEXPR RESULT)



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
// KResult
//////////////////////////////////////////////////////////////////////////////


    // _Kind is the super sort of _ and it contains term needs to be evaluated to _.
    syntax EvaledVarKind   ::= EvaledVar
    syntax EvaledExprKind  ::= EvaledExpr
    syntax TypeKind        ::= Type
    syntax EventParamsKind ::= EventParams
    syntax ParamsKind      ::= Params


    syntax KResult ::= EvaledVar
                     | EvaledExpr
                     | EvaledExprs
                     | TypedValue
                     | ValRecord
                     | Type
                     | EventParams
                     | Params


//////////////////////////////////////////////////////////////////////////////
// Program Loading
//////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#loadProgramAndInit" "(" Int "," Pgm ")"
 // ----------------------------------------------------------
    rule <k> #loadProgramAndInit(ACCTID, %pgm(ES, GS, DEFS, _))
            => #addEvents(ACCTID, ES) ~> #addGlobals(ACCTID, GS)
            ~> #addFuncs(ACCTID, (DEFS ++Def #mkPublicGetters(GS, .Defs)), 0)
         ... </k>


    // TODO: loadCode with init function
    syntax KItem ::= "#loadProgramAndInit" "(" Int "," Pgm "," Exprs ")"
 // --------------------------------------------------------------------


    syntax KItem ::= "#loadProgramWithoutInit" "(" Int "," Pgm ")"
 // --------------------------------------------------------------
    rule <k> #loadProgramWithoutInit(ACCTID, %pgm(ES, GS, DEFS, _))
            => #addEvents(ACCTID, ES)
            ~> #addFuncs(ACCTID, (DEFS ++Def #mkPublicGetters(GS, .Defs)), 0)
         ... </k>


// Event Declarations
// ==================


    syntax KItem ::= "#addEvents" "(" Int "," Events ")"
 // ----------------------------------------------------
    rule #addEvents(ACCTID, .Events) => .

    rule #addEvents(ACCTID, E ES) => #addEvent(ACCTID, E) ~> #addEvents(ACCTID, ES)


    syntax KItem ::= "#addEvent" "(" Int "," Event ")"
 // --------------------------------------------------
    rule <k> #addEvent(ACCTID, %event(EVENTNAME, EPARAMS))
            => #checkEventParams(EPARAMS, 0, .Ids)
            ~> #addEventAux(ACCTID, EVENTNAME, #parseTypeForEventParams(EPARAMS, .EventParams))
         ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <event> EVENTS </event>
           ...
         </account>
      requires notBool EVENTNAME in_keys(EVENTS)

    rule <k> #addEvent(ACCTID, %event(EVENTNAME, EPARAMS))
            => @staticException("Duplicate event name: " +String Id2String(EVENTNAME))
         ... </k>
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
       ~> #checkEventParams(EPARAMS, TOPICNUM +Int 1, NAME NAMES)
      requires TOPICNUM <Int 3

    rule #checkEventParams(%eparam(NAME, T, true) EPARAMS, TOPICNUM, NAMES)
        => @staticException("Maximum of 3 topics.")
      requires TOPICNUM >=Int 3

    rule #checkEventParams(%eparam(NAME, T, false) EPARAMS, TOPICNUM, NAMES)
        => #checkEventParam(%eparam(NAME, T, false), NAMES)
        ~> #checkEventParams(EPARAMS, TOPICNUM, NAME NAMES)


    syntax KItem ::= "#checkEventParam" "(" EventParam "," Ids ")"
 // --------------------------------------------------------------
    rule #checkEventParam(%eparam(NAME, T, ISTOPIC), NAMES)
        => #checkEventParamType(T, ISTOPIC)
        ~> #If notBool #isVarNameValid(NAME)
             #Then @staticException("Argument name invalid or reserved: " +String Id2String(NAME)) #Endif
        ~> #If #isInIds(NAME, NAMES)
             #Then @staticException("Duplicate function argument name: " +String Id2String(NAME)) #Endif


    syntax KItem ::= "#checkEventParamType" "(" Type "," Bool /*topic?*/ ")"
 // ------------------------------------------------------------------------
    rule #checkEventParamType(%bytesT(N), true) => .
      requires N <=Int 32

    rule #checkEventParamType(%bytesT(N), true) => @staticException("Indexed arguments are limited to 32 bytes.")
      requires N >Int 32

    rule #checkEventParamType(T, true) => .
      requires notBool isByteArrayType(T)

    rule #checkEventParamType(T, false) => .


    syntax KItem ::= "#addEventAux" "(" Int "," Id "," EventParamsKind ")"  [strict(3)]
 // -----------------------------------------------------------------------------------
    rule <k> #addEventAux(ACCTID, EVENTNAME, EPARAMS:EventParams) => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <event> EVENTS => EVENTS[EVENTNAME <- @event(EVENTNAME, EPARAMS)] </event>
           ...
         </account>


    syntax EventParamsKind ::= "#parseTypeForEventParams" "(" EventParams "," EventParams ")"
 // -----------------------------------------------------------------------------------------
    rule #parseTypeForEventParams(.EventParams, RESULT) => #revEventParams(RESULT, .EventParams)

    rule #parseTypeForEventParams(%eparam(NAME, T, ISTOPIC) EPARAMS, RESULT)
        => #parseTypeForEventParam(NAME, #parseType(T, true), ISTOPIC)
        ~> #parseTypeForEventParams(EPARAMS, RESULT)

    rule EPARAM:EventParam ~> #parseTypeForEventParams(EPARAMS, RESULT)
        => #parseTypeForEventParams(EPARAMS, EPARAM RESULT)


    syntax KItem ::= "#parseTypeForEventParam" "(" Id "," TypeKind "," Bool ")"  [strict(2)]
 // ----------------------------------------------------------------------------------------
    rule #parseTypeForEventParam(NAME, T:Type, TOPIC) => %eparam(NAME, T, TOPIC)


// Global Declarations
// ===================


    syntax KItem ::= "#addGlobals" "(" Int "," Globals ")"
 // ------------------------------------------------------
    rule #addGlobals(ACCTID, .Globals) => .

    rule #addGlobals(ACCTID, G GS) => #addGlobal(ACCTID, G) ~> #addGlobals(ACCTID, GS)


    syntax KItem ::= "#addGlobal" "(" Int "," Global ")"
 // ----------------------------------------------------
    rule <k> #addGlobal(ACCTID, %svdecl(VARNAME, T, _))
            => #If notBool #isVarNameValid(VARNAME)
                #Then @staticException("Variable name invalid or reserved: " +String Id2String(VARNAME)) #Endif
            ~> #addGlobalAux(ACCTID, VARNAME, #parseType(T, false))
         ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires notBool VARNAME in_keys(STORAGE)

    rule <k> #addGlobal(ACCTID, %svdecl(VARNAME, T, _))
            => @staticException("Cannot declare a persistent variable twice! " +String Id2String(VARNAME))
         ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires VARNAME in_keys(STORAGE)


    syntax KItem ::= "#addGlobalAux" "(" Int "," Id "," TypeKind ")"  [strict(3)]
 // -----------------------------------------------------------------------------
    rule <k> #addGlobalAux(ACCTID, VARNAME, T:Type) => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE
                    => STORAGE[VARNAME <- @val(#defaultTypedValue(T), true)] </storage>
           ...
         </account>


// Function Declarations
// =====================


    syntax KItem ::= "#addFuncs" "(" Int "," Defs "," Int /*order*/ ")"
 // -------------------------------------------------------------------
    rule #addFuncs(ACCTID, .Defs, _) => .

    rule #addFuncs(ACCTID, %fdecl(DECS, FUNCNAME, PARAMS, T, FUNCBODY) DEFS, ORDER)
        => #addFunc(ACCTID, FUNCNAME, PARAMS, T, FUNCBODY,
                    #isInDecorators(%@constant, DECS),
                    #isInDecorators(%@payable , DECS),
                    #isInDecorators(%@private , DECS),
                    #isInDecorators(%@public  , DECS),
                    ORDER)
        ~> #addFuncs(ACCTID, DEFS, ORDER +Int 1)


    syntax KItem ::= "#addFunc" "(" Int "," Id "," Params "," Type "," Stmts "," Bool "," Bool "," Bool "," Bool "," Int ")"
 // ------------------------------------------------------------------------------------------------------------------------
    rule <k> #addFunc(ACCTID, FUNCNAME, PARAMS, RT, FUNCBODY, CONSTANT, PAYABLE, PRIVATE, PUBLIC, ORDER)
            => #checkFuncParams(ACCTID, PARAMS, .Ids)
            ~> #checkPrivatePublicMECE(PRIVATE, PUBLIC)
            ~> #addFuncAux(ACCTID, FUNCNAME,
                           #parseTypeForParams(PARAMS, .Params),
                           #parseType(RT, true),
                           FUNCBODY,
                           CONSTANT, PAYABLE, PRIVATE, ORDER)
         ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <fun> FUNCS </fun>
           <event> EVENTS </event>
           ...
         </account>
      requires notBool(FUNCNAME in_keys(FUNCS)) andBool notBool(FUNCNAME in_keys(EVENTS))

    rule <k> #addFunc(ACCTID, FUNCNAME, PARAMS, RT, FUNCBODY, CONSTANT, PAYABLE, PRIVATE, PUBLIC, ORDER)
            => @staticException("Duplicate event or function name: " +String Id2String(FUNCNAME))
         ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <fun> FUNCS </fun>
           <event> EVENTS </event>
           ...
         </account>
      requires (FUNCNAME in_keys(FUNCS)) orBool (FUNCNAME in_keys(EVENTS))


    syntax KItem ::= "#checkFuncParams" "(" Int "," Params "," Ids ")"
 // ------------------------------------------------------------------
    rule #checkFuncParams(ACCTID, .Params, NAMES) => .

    rule #checkFuncParams(ACCTID, %param(NAME, T) PARAMS, NAMES)
        => #checkFuncParam(ACCTID, %param(NAME, T), NAMES)
        ~> #checkFuncParams(ACCTID, PARAMS, NAME NAMES)


    syntax KItem ::= "#checkFuncParam" "(" Int "," Param "," Ids ")"
 // ----------------------------------------------------------------
     rule #checkFuncParam(ACCTID, %param(NAME, _), NAMES)
        => #checkVarName(ACCTID, NAME)
        ~> #If #isInIds(NAME, NAMES)
             #Then @staticException("Duplicate function argument name: " +String Id2String(NAME)) #Endif


    syntax KItem ::= "#checkPrivatePublicMECE" "(" Bool /*private?*/ "," Bool /*public?*/ ")"
 // -----------------------------------------------------------------------------------------
    rule #checkPrivatePublicMECE(PRIVATE, PUBLIC)
        => #If PRIVATE ==K true andBool PUBLIC ==K true
             #Then @staticException("Cannot use public and private decorators on the same function.") #Endif
        ~> #If PRIVATE ==K false andBool PUBLIC ==K false
             #Then @staticException("Function visibility must be declared (@public or @private).") #Endif


    syntax KItem ::= "#addFuncAux" "(" Int "," Id "," ParamsKind "," TypeKind "," Stmts "," Bool "," Bool "," Bool "," Int ")"  [seqstrict(3, 4)]
 // ---------------------------------------------------------------------------------------------------------------------------------------------
    rule <k> #addFuncAux(ACCTID, FUNCNAME, PARAMS:Params, RT:Type, FUNCBODY, CONSTANT, PAYABLE, PRIVATE, ORDER) => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <fun> FUNCS
                => FUNCS[FUNCNAME <- @func(FUNCNAME, PARAMS, RT, FUNCBODY, CONSTANT, PAYABLE, PRIVATE, ORDER)] </fun>
           ...
         </account>


    syntax ParamsKind ::= "#parseTypeForParams" "(" Params "," Params ")"
 // ---------------------------------------------------------------------
    rule #parseTypeForParams(.Params, RESULT) => #revParams(RESULT, .Params)

    rule #parseTypeForParams(%param(NAME, T) PARAMS, RESULT)
        => #parseTypeForParam(NAME, #parseType(T, true))
        ~> #parseTypeForParams(PARAMS, RESULT)

    rule PARAM:Param ~> #parseTypeForParams(PARAMS, RESULT)
        => #parseTypeForParams(PARAMS, PARAM RESULT)


    syntax KItem ::= "#parseTypeForParam"  "(" Id "," TypeKind ")"  [strict(2)]
 // ---------------------------------------------------------------------------
    rule #parseTypeForParam(NAME, T:Type) => %param(NAME, T)


//////////////////////////////////////////////////////////////////////////////
// Statements
//////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#evalStmts" "(" Stmts ")"
 // -------------------------------------------
    rule #evalStmts(.Stmts) => .

    rule #evalStmts(STMT:Stmt STMTS:Stmts) => #evalStmt(STMT) ~> #evalStmts(STMTS)


    syntax KItem ::= "#evalStmt" "(" Stmt ")"
 // -----------------------------------------


// Annotated Var
// -------------

    rule #evalStmt(%annvar(VARNAME, T)) => #newVar(VARNAME, #parseType(T, true))


    syntax KItem ::= "#newVar"    "(" Id "," K /*Type*/ ")"  [strict(2)]
    syntax KItem ::= "#newVarAux" "(" Id "," Type ")"
 // --------------------------------------------------------------------
    rule <k> #newVar(VARNAME, T)
            => #checkVarName(ACCTID, VARNAME) ~> #newVarAux(VARNAME, T)
         ... </k>
         <id> ACCTID </id>

    rule <k> #newVarAux(VARNAME, T)
            => @staticException("Duplicate variable name: " +String Id2String(VARNAME))
         ... </k>
         <memory> MEM </memory>
      requires VARNAME in_keys(MEM)

    rule <k> #newVarAux(VARNAME, T) => . ... </k>
         <memory> MEM => MEM[VARNAME <- @val(#defaultTypedValue(T), true)] </memory>
      requires notBool VARNAME in_keys(MEM)


// Annotated Assignment
// --------------------

    rule #evalStmt(%annassign(VARNAME, T, EXPR))
        => #annassign(VARNAME, #parseType(T, true), #evalExpr(EXPR))


    syntax KItem ::= "#annassign" "(" Id "," TypeKind "," K /*EvaledExpr*/ ")"  [seqstrict(2,3)]
 // --------------------------------------------------------------------------------------------
    rule #annassign(VARNAME, VARTYPE:Type, @ee(EXPRTYPE, VALUE, LITERAL))
        => #newVar(VARNAME, VARTYPE)
        ~> #assignTo(@ee(EXPRTYPE, VALUE, LITERAL), @%var(VARNAME))


// Assignment
// ----------


    rule #evalStmt(%assign(VAR, EXPR)) => #assignTo(#evalExpr(EXPR), #getAssignTarget(VAR))


    syntax KItem ::= "#assignTo"    "(" K /*EvaledExpr*/ "," K /*EvaledVar*/ ")"          [seqstrict]
    syntax KItem ::= "#assignToAux" "(" EvaledExpr "," EvaledVar "," K /*ValRecord*/ ")"  [strict(3)]
 // -------------------------------------------------------------------------------------------------
    rule #assignTo(EEXPR:EvaledExpr, EVAR:EvaledVar)
        => #assignToAux(EEXPR, EVAR, #lookupVar(EVAR))

    rule #assignToAux(EEXPR, EVAR, @val(_, false))
        => @staticException("Cannot modify function argument.")

    rule #assignToAux(EEXPR, EVAR, @val(@tv(TYPE, _), true))
        => #assignToHelper(EVAR, #baseTypeConvert(EEXPR, TYPE))
      requires isBaseType(TYPE)


    syntax KItem ::= "#assignToHelper" "(" EvaledVar "," K ")"  [strict(2)]
 // -----------------------------------------------------------------------
    rule <k> #assignToHelper(@%var(VARNAME), TVNEW:TypedValue) => . ... </k>
         <memory> MEM => MEM[VARNAME <- @val(TVNEW, true)] </memory>

    rule <k> #assignToHelper(@%svar(VARNAME), TVNEW:TypedValue) => . ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE => STORAGE[VARNAME <- @val(TVNEW, true)] </storage>
           ...
         </account>


    rule #assignToHelper(@%subscript(EVAR, OFFSETEXPR), TVNEW)
        => #assignToHelper(EVAR, #updateValue(#lookupVar(EVAR), OFFSETEXPR, TVNEW))


    syntax KItem /*TypedValue*/ ::= "#updateValue" "(" K /*ValRecord*/ "," K /*offset*/ "," TypedValue ")"  [strict(1)]
 // -------------------------------------------------------------------------------------------------------------------
    rule #updateValue(@val(@tv(%mapT(KT, VT), MAPVALUE:Map), _), KEYEXPR:EvaledExpr, TVNEW)
        => #updateMapValue(@tv(%mapT(KT, VT), MAPVALUE), #baseTypeConvert(KEYEXPR, KT), TVNEW)
      requires isBaseType(KT)


    syntax KItem /*TypedValue*/ ::= "#updateMapValue" "(" TypedValue "," K /*key*/ "," TypedValue ")"  [strict(2)]
 // --------------------------------------------------------------------------------------------------------------
    rule #updateMapValue(@tv(T, MAP:Map), @tv(KT, OFFSET), TV) => @tv(T, MAP[OFFSET <- TV])


    syntax KItem /*EvaledVar*/ ::= "#getAssignTarget" "(" Var ")"
 // -------------------------------------------------------------
    rule <k> #getAssignTarget(%var(VARNAME))
            => #If %var(VARNAME) in FORVARS
                 #Then @staticException("Altering iterator which is in use!") #Endif
            ~> #If %var(VARNAME) in INLOOP
                 #Then @staticException("Altering list which is being iterated!") #Endif
            ~> #evalVar(%var(VARNAME))
         ... </k>
         <forvar> FORVARS </forvar>
         <inLoop> INLOOP </inLoop>

    rule <k> #getAssignTarget(%svar(VARNAME))
            => #If CONSTANT ==K true
                 #Then @staticException("Cannot modify storage inside a constant function") #Endif
            ~> #If %var(VARNAME) in INLOOP
                 #Then @staticException("Altering list which is being iterated!") #Endif
            ~> #evalVar(%svar(VARNAME))
         ... </k>
         <constant> CONSTANT </constant>
         <inLoop> INLOOP </inLoop>

    rule <k> #getAssignTarget(%subscript(VAR, INDEX))
            => #If VAR in INLOOP
                 #Then @staticException("Altering list which is being iterated!") #Endif
            ~> #evalVar(%subscript(VAR, INDEX))
         ... </k>
         <inLoop> INLOOP </inLoop>

    rule <k> #getAssignTarget(%attribute(VAR, FIELDNAME))
            => #If %attribute(VAR, FIELDNAME) in INLOOP
                 #Then @staticException("Altering list which is being iterated!") #Endif
            ~> #evalVar(%attribute(VAR, FIELDNAME))
         ... </k>
         <inLoop> INLOOP </inLoop>


// Return
// ------

    rule <k> #evalStmt(%return(EXPR)) => #return(#evalExpr(EXPR), T) ... </k>
         <return> T </return>
      requires T =/=K %void

    rule <k> #evalStmt(%return(EXPR))
            => @staticException("Not expecting to return a value") ... </k>
         <return> %void </return>


    syntax KItem ::= "#return"
 // --------------------------


    syntax KItem ::= "#return" "(" K "," Type ")"  [strict]
 // -------------------------------------------------------
    rule #return(@ee(ACTUALTYPE, VALUE, LITERAL), EXPECTEDTYPE)
        => #If notBool #areUnitsCompatible(ACTUALTYPE, LITERAL, EXPECTEDTYPE)
             #Then @staticException("Return type units mismatch.") #Endif
        ~> #returnBaseType(@ee(ACTUALTYPE, VALUE, LITERAL), EXPECTEDTYPE)
      requires isBaseType(ACTUALTYPE)


    syntax KItem ::= "#returnBaseType" "(" EvaledExpr "," Type ")"
 // --------------------------------------------------------------
    rule #returnBaseType(@ee(ACTUALTYPE, VALUE, LITERAL), EXPECTEDTYPE)
        => #dropSubstate ~> #dropWorldState ~> #popCallStack(@ee(EXPECTEDTYPE, VALUE, LITERAL))
      requires #dropUnit(ACTUALTYPE) ==K #dropUnit(EXPECTEDTYPE)

    rule #returnBaseType(@ee(ACTUALTYPE, VALUE, LITERAL), EXPECTEDTYPE)
        => #dropSubstate ~> #dropWorldState ~> #popCallStack(@ee(EXPECTEDTYPE, VALUE, LITERAL))
      requires #dropUnit(ACTUALTYPE) ==K %num andBool #dropUnit(EXPECTEDTYPE) ==K %signed256


//////////////////////////////////////////////////////////////////////////////
// Expressions
//////////////////////////////////////////////////////////////////////////////


    syntax KItem /*EvaledExpr*/  ::= "#evalExpr" "(" Expr ")"
    syntax KItem /*EvaledExprs*/ ::= "#evalExprs" "(" Exprs "," EvaledExprs ")"
 // ---------------------------------------------------------------------------
    rule #evalExprs(.Exprs, RESULT) => #revEvaledExprs(RESULT, .EvaledExprs)

    rule #evalExprs((EXPR:Expr EXPRS:Exprs), RESULT) => #evalExpr(EXPR) ~> #evalExprs(EXPRS, RESULT)

    rule EEXPR:EvaledExpr ~> #evalExprs(EXPRS, RESULT) => #evalExprs(EXPRS, EEXPR RESULT)


// Constants
// =========


    rule #evalExpr(I:Int) => @ee(%num, I, true)

    rule #evalExpr(%hex(STR:String)) => @ee(%address, #parseHexWord(STR), true)
      requires lengthString(STR) ==K 42

    rule #evalExpr(%hex(STR:String)) => @ee(%bytes32, #parseHexWord(STR), true)
      requires lengthString(STR) ==K 66


// Variable
// ========


    rule #evalExpr(VAR:Var) => #var(#evalVar(VAR))


    syntax KItem ::= "#var" "(" K ")"     [strict]
    syntax KItem ::= "#varAux" "(" K ")"  [strict]
 // ----------------------------------------------
    rule #var(EVAR:EvaledVar) => #varAux(#lookupVar(EVAR))

    rule #varAux(@val(@tv(T, V), _)) => @ee(T, V, false)


    syntax KItem /*EvaledVar*/ ::= "#evalVar" "(" Var ")"
    syntax KItem /*EvaledVar*/ ::= "#evalSubscriptVar" "(" K "," K ")"   [seqstrict]
    syntax KItem /*EvaledVar*/ ::= "#evalAttributeVar" "(" K "," Id ")"  [strict(1)]
 // --------------------------------------------------------------------------------
    rule #evalVar(%var(VARNAME)) => @%var(VARNAME)

    rule #evalVar(%svar(VARNAME)) => @%svar(VARNAME)

    rule #evalVar(%subscript(VAR, EXPR)) => #evalSubscriptVar(#evalVar(VAR), #evalExpr(EXPR))

    rule #evalVar(%attribute(VAR, FIELDNAME)) => #evalAttributeVar(#evalVar(VAR), FIELDNAME)

    rule #evalSubscriptVar(EVAR:EvaledVar, EEXPR:EvaledExpr) =>  @%subscript(EVAR, EEXPR)

    rule #evalAttributeVar(EVAR:EvaledVar, FIELDNAME) => @%attribute(EVAR, FIELDNAME)


// Function Call
// =============


    rule <k> #evalExpr(%ecall(ADDR, FUNCNAME, EXPRS))
            => #ecall(#evalExpr(ADDR), FUNCNAME, #evalExprs(EXPRS, .EvaledExprs))
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID>   ACCTID   </acctID>
           <external> EXTERNAL </external>
           ...
         </account>
      requires FUNCNAME in_keys(EXTERNAL)


    syntax KItem ::= "#ecall" "(" K  "," Id "," K ")"  [seqstrict(1, 3)]
 // --------------------------------------------------------------------
    rule <k> #ecall(@ee(%address, ACCTTO, _), FUNCNAME, EARGS:EvaledExprs)
            => #call(ACCTFROM, ACCTTO, 0, FUNCNAME, EARGS)
         ... </k>
         <id> ACCTFROM </id>


    syntax KItem ::= "#call" "(" Int "," Int "," Int "," Id "," EvaledExprs ")"
    syntax KItem ::= "#callWithCode" "(" Int "," Int "," Int "," FuncRecord "," EvaledExprs ")"
 // -------------------------------------------------------------------------------------------
    rule <k> #call(ACCTFROM, ACCTTO, VALUE, FUNCNAME, EARGS)
            => #callWithCode(ACCTFROM, ACCTTO, VALUE, FUNCRECORD, EARGS)
         ... </k>
         <account>
           <acctID> ACCTTO </acctID>
           <fun> FUNCNAME |-> FUNCRECORD _:Map </fun>
           ...
         </account>

    rule <k> #call(ACCTFROM, ACCTTO, VALUE, FUNCNAME, EARGS)
            => @dynamicException("Function " +String Id2String(FUNCNAME) +String " not declared yet.")
         ... </k>
         <account>
           <acctID> ACCTTO </acctID>
           <fun> FUN </fun>
           ...
         </account>
       requires notBool FUNCNAME in_keys(FUN)

    rule <k> (#callWithCode(ACCTFROM, ACCTTO, VALUE, FUNCRECORD, EARGS) ~> RESTPGM)
            => #checkFuncOrder(ACCTFROM, ORDER, ACCTTO, FUNCRECORD)
            ~> #pushCallStack(RESTPGM) ~> #pushWorldState ~> #pushSubstate
            ~> #transferFunds(ACCTFROM, ACCTTO, VALUE)
            ~> #mkCall(ACCTFROM, ACCTTO, VALUE, FUNCRECORD, EARGS) </k>
         <order> ORDER </order>


    syntax KItem ::= "#checkFuncOrder" "(" Int "," Int "," Int "," FuncRecord ")"
 // -----------------------------------------------------------------------------
    rule #checkFuncOrder(ACCTFROM, FROMORDER, ACCTTO, @func(FUNCNAME, _, _, _, _, _, _, TOORDER))
        => #If (ACCTFROM ==K ACCTTO) andBool (FROMORDER <Int TOORDER) andBool (FROMORDER =/=Int -1)
             #Then @staticException("Function " +String Id2String(FUNCNAME) +String " is called before being declared.") #Endif


    syntax KItem ::= "#transferFunds" "(" Int "," Int "," Int ")"
 // -------------------------------------------------------------
    rule <k> #transferFunds(ACCTFROM, ACCTTO, VALUE) => . ... </k>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> ORIGFROM => ORIGFROM -Int VALUE </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> ORIGTO => ORIGTO +Int VALUE </balance>
           ...
         </account>
      requires ACCTFROM =/=K ACCTTO andBool VALUE <=Int ORIGFROM

    rule <k> #transferFunds(ACCTFROM, ACCTTO, VALUE)
            => @dynamicException("Balance of account " +String Int2String(ACCTFROM) +String " is not sufficient.") ... </k>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> ORIGFROM </balance>
           ...
         </account>
      requires VALUE >Int ORIGFROM

   rule <k>  (. => #newAccount(ACCTTO)) ~> #transferFunds(ACCTFROM, ACCTTO, VALUE) ... </k>
        <activeAccounts> ACCTS </activeAccounts>
      requires (ACCTFROM =/=K ACCTTO) andBool (notBool(ACCTTO in ACCTS))

    rule <k> #transferFunds(ACCT, ACCT, VALUE) => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> ORIGFROM </balance>
           ...
         </account>
      requires VALUE <=Int ORIGFROM


    syntax KItem ::= "#mkCall" "(" Int "," Int "," Int "," FuncRecord "," EvaledExprs ")"
 // -------------------------------------------------------------------------------------
    rule <k> #mkCall(ACCTFROM, ACCTTO, VALUE, @func(FUNCNAME, PARAMS, RT, STMTS, CONSTANT, PAYABLE, PRIVATE, ORDER), EARGS)
            => #initCall ~> #checkFuncPayable(PAYABLE) ~> #checkFuncPrivate(PRIVATE)
            ~> #If #numOfParams(PARAMS) =/=Int #numOfEvaledExprs(EARGS)
                 #Then @staticException("# of args doesn't match # of params in function" +String Id2String(FUNCNAME)) #Endif
            ~> #bindParams(PARAMS, EARGS)
            ~> #evalStmts(STMTS)
            ~> #return
         ... </k>
         <constant>  _ => CONSTANT </constant>
         <return>    _ => RT       </return>
         <order>     _ => ORDER    </order>
         <id>        _ => ACCTTO   </id>
         <caller>    _ => ACCTFROM </caller>
         <callValue> _ => VALUE    </callValue>


    syntax KItem ::= "#initCall"
 // ----------------------------
    rule <k> #initCall => . ... </k>
         <memory>   _ => .Map  </memory>
         <memStack> _ => .List </memStack>
         <forLoop>
           <forvar> _ => .Set </forvar>
           <inLoop> _ => .Set </inLoop>
         </forLoop>


    syntax KItem ::= "#checkFuncPayable" "(" Bool ")"
 // -------------------------------------------------
    rule #checkFuncPayable(true) => .

    rule <k> #checkFuncPayable(false) => . ... </k>
         <callValue> 0 </callValue>

    rule <k> #checkFuncPayable(false) => @dynamicException("Can not send value to a non-payable function.") ... </k>
         <callValue> CV </callValue>
      requires CV =/=K 0


    syntax KItem ::= "#checkFuncPrivate" "(" Bool ")"
 // ------------------------------------------------
    rule #checkFuncPrivate(false) => .

    rule <k> #checkFuncPrivate(true) => . ...</k>
         <id>     ACCTTO   </id>
         <caller> ACCTFROM </caller>
      requires ACCTTO ==K ACCTFROM

    rule <k> #checkFuncPrivate(true) => @dynamicException("Can not call a private function from another account.") ... </k>
         <id>     ACCTTO   </id>
         <caller> ACCTFROM </caller>
      requires ACCTTO =/=K ACCTFROM


    syntax KItem ::= "#bindParams" "(" Params "," EvaledExprs ")"
 // -------------------------------------------------------------
    rule #bindParams(.Params, .EvaledExprs) => .

    rule #bindParams(PARAM PARAMS, EEXPR EEXPRS)
        => #bindParam(PARAM, EEXPR)
        ~> #bindParams(PARAMS, EEXPRS)


    syntax KItem ::= "#bindParam" "(" Param "," EvaledExpr ")"
 // ----------------------------------------------------------
    rule #bindParam(%param(NAME, T), EEXPR) => #annassign(NAME, T, EEXPR)
      requires isBaseType(T)


// Reserved Expression
// --------------------

    // as_num256
    syntax KItem /*EvaledExpr*/ ::= "#asNum256" "(" K ")"  [strict]
 // ---------------------------------------------------------------
   rule #evalExpr(%as_num256(EXPR)) => #asNum256(#evalExpr(EXPR))

   rule #asNum256(@ee(T, VALUE, _))
       => #If notBool(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %address))
            #Then @staticException("Function arg type does not match expected type.") #Endif
       ~> #checkInRangeNum256(VALUE)
       ~> @ee(%num256, VALUE, false)


//////////////////////////////////////////////////////////////////////////////
// Clear State
//////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#clearVyperState"
 // -----------------------------------
    rule <k> #clearVyperState => . ... </k>
         <callStack>     _ => .List </callStack>
         <interimStates> _ => .List </interimStates>
         <memory>        _ => .Map  </memory>
         <memStack>      _ => .List </memStack>
         <forvar>        _ => .Set  </forvar>
         <inLoop>        _ => .Set  </inLoop>
         <constant>      _ => false </constant>
         <return>        _ => %void </return>
         <id>            _ => 0     </id>
         <caller>        _ => 0     </caller>
         <callValue>     _ => 0     </callValue>
         <selfDestruct>  _ => .Set  </selfDestruct>
         <log>           _ => .List </log>


///////////////////////////////////////////////////////////////////////////////
// Types
///////////////////////////////////////////////////////////////////////////////


// Default Values
// ==============

    syntax TypedValue ::= "#defaultTypedValue" "(" Type ")"  [function]
 // -------------------------------------------------------------------
    rule #defaultTypedValue(%bool) => @tv(%bool, false)

    rule #defaultTypedValue(%num) => @tv(%num, 0)

    rule #defaultTypedValue(%decimal) => @tv(%decimal, @d(0))

    rule #defaultTypedValue(%unitT(%num, UNIT:Map, POSITIONAL)) => @tv(%unitT(%num, UNIT, POSITIONAL), 0)

    rule #defaultTypedValue(%unitT(%decimal, UNIT:Map, POSITIONAL)) => @tv(%unitT(%decimal, UNIT, POSITIONAL), @d(0))

    rule #defaultTypedValue(%num256) => @tv(%num256, 0)

    rule #defaultTypedValue(%signed256) => @tv(%signed256, 0)

    rule #defaultTypedValue(%bytes32) => @tv(%bytes32, 0)

    rule #defaultTypedValue(%address) => @tv(%address, 0)

    rule #defaultTypedValue(%bytesT(N)) => @tv(%bytesT(N), "")

    rule #defaultTypedValue(%listT(SUBTYPE, LEN)) => @tv(%listT(SUBTYPE, LEN), #defaultValueListType(SUBTYPE, LEN, 0))

    rule #defaultTypedValue(%mapT(KT, VT)) => @tv(%mapT(KT, VT), .Map)

    rule #defaultTypedValue(%structT(ANNVARS)) => @tv(%structT(ANNVARS), #defaultValueStructType(ANNVARS))


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


    syntax TypeKind ::= "#parseType" "(" Type "," Bool /*in memory?*/ ")"
 // ---------------------------------------------------------------------
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
        => @staticException("Arrays must have a positive integral number of elements.")
      requires N <=Int 0

    rule #parseType(%bytesT(N), _) => %bytesT(N)
      requires N >Int 0

    rule #parseType(%listT(SUBTYPE, N), INMEMORY)
        => #parseListType(#parseType(SUBTYPE, INMEMORY), N)

    rule #parseType(%mapT(KT, VT), false)
        => #parseMapType(#parseType(KT, false), #parseType(VT, false))
      requires isBaseType(KT) orBool isByteArrayType(KT)

    rule #parseType(%mapT(KT, VT), false)
        => @staticException("Mapping keys must be base or bytes types")
      requires notBool(isBaseType(KT) orBool isByteArrayType(KT))

    rule #parseType(%structT(ANNVARS), INMEMORY)
        => #parseStructType(ANNVARS, INMEMORY)

    // TODO: support Tuple

    // Special Types
    rule #parseType(%timestamp, _)       => %unitT(%num, %sec |-> 1, true)

    rule #parseType(%timedelta, _)       => %unitT(%num, %sec |-> 1, false)

    rule #parseType(%currency_value, _)  => %unitT(%num, %currency |-> 1, false)

    rule #parseType(%currency1_value, _) => %unitT(%num, %currency1 |-> 1, false)

    rule #parseType(%currency2_value, _) => %unitT(%num, %currency2 |-> 1, false)

    rule #parseType(%wei_value, _)       => %unitT(%num, %wei |-> 1, false)


    syntax TypeKind ::= "#parseListType" "(" TypeKind "," Int ")"  [strict(1)]
 // --------------------------------------------------------------------------
    rule #parseListType(T, N) => %listT(T, N)


    syntax TypeKind ::= "#parseMapType" "(" TypeKind "," TypeKind ")"  [seqstrict]
 // ------------------------------------------------------------------------------
    rule #parseMapType(KT, VT) => %mapT(KT, VT)


    syntax TypeKind ::= "#parseStructType"    "(" AnnVars "," Bool ")"
    syntax TypeKind ::= "#parseStructTypeAux" "(" AnnVars "," Bool "," Ids "," AnnVars")"
 // -------------------------------------------------------------------------------------
    rule #parseStructType(ANNVARS, INMEMORY)
        => #parseStructTypeAux(ANNVARS, INMEMORY, #getFieldNames(ANNVARS), .AnnVars)

    rule #parseStructTypeAux(.AnnVars, _, _, ANNVARS) => %structT(#revAnnVars(ANNVARS, .AnnVars))

    rule #parseStructTypeAux(%annvar(FIELDNAME, T) ANNVARS, INMEMORY, FIELDNAMES, RESULT)
        => #parseTypeForField(FIELDNAME, #parseType(T, INMEMORY), FIELDNAMES)
        ~> #parseStructTypeAux(ANNVARS, INMEMORY, FIELDNAMES, RESULT)

    rule %annvar(FIELDNAME, T) ~> #parseStructTypeAux(ANNVARS, INMEMORY, FIELDNAMES, RESULT)
        => #parseStructTypeAux(ANNVARS, INMEMORY, FIELDNAME FIELDNAMES, %annvar(FIELDNAME, T) RESULT)


    syntax Ids ::= "#getFieldNames" "(" AnnVars ")"  [function]
 // -----------------------------------------------------------
    rule #getFieldNames(.AnnVars) => .Ids

    rule #getFieldNames(%annvar(FIELDNAME, _) ANNVARS)
        => FIELDNAME #getFieldNames(ANNVARS)


    syntax KItem ::= "#parseTypeForField" "(" Id "," TypeKind "," Ids ")"  [strict(2)]
 // ----------------------------------------------------------------------------------
    rule #parseTypeForField(FIELDNAME, T, _)
        => @staticException("Invalid member variable for struct.")
      requires notBool #isVarNameValid(FIELDNAME)

    rule #parseTypeForField(FIELDNAME, T, FIELDNAMES)
        => @staticException("Member variable duplicated: " +String Id2String(FIELDNAME))
      requires #isInIds(FIELDNAME, FIELDNAMES)

    rule #parseTypeForField(FIELDNAME, T, FIELDNAMES)
        => %annvar(FIELDNAME, T)
      requires #isVarNameValid(FIELDNAME) andBool notBool(#isInIds(FIELDNAME, FIELDNAMES))


// Units
// =====


    syntax UnitType ::= "%unitT" "(" PureNumType "," Map "," Bool /*positional*/ ")"  // internal representation of unit type


    syntax KItem /*Type*/ ::= "#parseUnitType" "(" UnitType ")"
 // -----------------------------------------------------------


    syntax Bool ::= "#areUnitsCompatible" "(" Type /*from*/ "," Bool /*from literal?*/ "," Type /*to*/ ")"    [function]
 // --------------------------------------------------------------------------------------------------------------------
    rule #areUnitsCompatible(FROMTYPE, _, TOTYPE) => true
      requires notBool(isUnitType(FROMTYPE)) andBool notBool(isUnitType(TOTYPE))

    rule #areUnitsCompatible(FROMTYPE, true, TOTYPE) => true
      requires notBool(isUnitType(FROMTYPE)) andBool isUnitType(TOTYPE)

    rule #areUnitsCompatible(FROMTYPE, false, TOTYPE) => false
      requires notBool(isUnitType(FROMTYPE)) andBool isUnitType(TOTYPE)

    rule #areUnitsCompatible(FROMTYPE, _, TOTYPE) => false
      requires isUnitType(FROMTYPE) andBool notBool(isUnitType(TOTYPE))

    rule #areUnitsCompatible(%unitT(_, FROMMAP:Map, FROMPOSITIONAL), _, %unitT(_, TOMAP:Map, TOPOSITIONAL))
        => true
      requires FROMMAP ==K TOMAP andBool FROMPOSITIONAL ==K TOPOSITIONAL

    rule #areUnitsCompatible(%unitT(_, FROMMAP:Map, FROMPOSITIONAL), _, %unitT(_, TOMAP:Map, TOPOSITIONAL))
        => false
      requires FROMMAP =/=K TOMAP orBool FROMPOSITIONAL =/=K TOPOSITIONAL


    syntax Type ::= "#dropUnit" "(" Type ")"    [function]
 // ------------------------------------------------------
    rule #dropUnit(T) => T
      requires notBool isUnitType(T)

    rule #dropUnit(%unitT(%num, _:Map, _)) => %num

    rule #dropUnit(%unitT(%decimal, _:Map, _)) => %decimal



// Type Utils
// ==========


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


    syntax KItem /*TypedValue*/ ::= "#baseTypeConvert" "(" EvaledExpr "," Type ")"
 // ------------------------------------------------------------------------------
    rule #baseTypeConvert(@ee(FROMTYPE, VALUE, LITERAL), TOTYPE)
        => #If notBool #areUnitsCompatible(FROMTYPE, LITERAL, TOTYPE)
             #Then @staticException("Base type conversion unavailable due to incompatible units") #Endif
        ~> #baseTypeConvertAux(#baseTypeConvertNoUnit(#dropUnit(FROMTYPE), VALUE, #dropUnit(TOTYPE)), TOTYPE)


    syntax KItem /*TypedValue*/ ::= "#baseTypeConvertAux" "(" K /*TypedValue*/ "," Type ")"  [strict(1)]
 // ---------------------------------------------------------------------------------------------------
    rule #baseTypeConvertAux(@tv(_, VALUE), TOTYPE) => @tv(TOTYPE, VALUE)


    syntax KItem /*TypedValue*/ ::= "#baseTypeConvertNoUnit" "(" Type /*from*/ "," Value "," Type /*to*/ ")"
 // --------------------------------------------------------------------------------------------------------
    rule #baseTypeConvertNoUnit(TOTYPE, VALUE, TOTYPE) => @tv(TOTYPE, VALUE)
      requires isBaseType(TOTYPE)

    rule #baseTypeConvertNoUnit(FROMTYPE, VALUE, TOTYPE) => @staticException("Base type conversion from or to non-base type.")
      requires (notBool isBaseType(FROMTYPE)) orBool (notBool isBaseType(TOTYPE))

    rule #baseTypeConvertNoUnit(%num, VALUE, %decimal) => @tv(%decimal, VALUE *Int @decimalDivisor)

    rule #baseTypeConvertNoUnit(%num256, VALUE, %num) => #checkInRangeNum(VALUE) ~> @tv(%num256, VALUE)

    rule #baseTypeConvertNoUnit(FROMTYPE, VALUE, TOTYPE) => @staticException("Typecasting unavailable.")
      requires isBaseType(FROMTYPE) andBool isBaseType(TOTYPE)
               andBool (FROMTYPE =/=K TOTYPE)
               andBool notBool(FROMTYPE ==K %num andBool TOTYPE ==K %decimal)
               andBool notBool(FROMTYPE ==K %num256 andBool TOTYPE ==K %num)


///////////////////////////////////////////////////////////////////////////////
// Call Stack
///////////////////////////////////////////////////////////////////////////////


    syntax State ::= "@vyper" "(" Int  "," K "," Map "," List "," Set "," Set "," Bool "," Type "," Int "," Int "," Int ")"
 // -----------------------------------------------------------------------------------------------------------------------


    syntax KItem ::= "#pushCallStack" "(" K ")"
 // -------------------------------------------
    rule <k> #pushCallStack(RESTPGM) => . ... </k>
         <callStack> (.List
                    => ListItem(@vyper(ACCTID, RESTPGM, MEM, MEMSTACK, FORVAR, INLOOP, CONSTANT, RT, ORDER, CR, CV)))
         ... </callStack>
         <memory>   MEM      </memory>
         <memStack> MEMSTACK </memStack>
         <forLoop>
           <forvar> FORVAR </forvar>
           <inLoop> INLOOP </inLoop>
         </forLoop>
         <constant>  CONSTANT </constant>
         <return>    RT       </return>
         <order>     ORDER    </order>
         <id>        ACCTID   </id>
         <caller>    CR       </caller>
         <callValue> CV       </callValue>


    syntax KItem ::= "#popCallStack" "(" EvaledExpr ")"
 // ---------------------------------------------------
    rule <k> #popCallStack(EEXPR) ~> _  => EEXPR ~> RESTPGM </k>
         <callStack> (ListItem(@vyper(ACCTID, RESTPGM, MEM, MEMSTACK, FORVAR, INLOOP, CONSTANT, RT, ORDER, CR, CV))
                    => .List)
         ... </callStack>
         <memory>   _ => MEM      </memory>
         <memStack> _ => MEMSTACK </memStack>
         <forLoop>
           <forvar> _ => FORVAR </forvar>
           <inLoop> _ => INLOOP </inLoop>
         </forLoop>
         <constant>  _ => CONSTANT </constant>
         <return>    _ => RT       </return>
         <order>     _ => ORDER    </order>
         <id>        _ => ACCTID   </id>
         <caller>    _ => CR       </caller>
         <callValue> _ => CV       </callValue>



///////////////////////////////////////////////////////////////////////////////
// World State
///////////////////////////////////////////////////////////////////////////////


    syntax Account ::= "@account" "(" Int "," Int "," Map "," Map "," Map "," Map ")"
 // ---------------------------------------------------------------------------------


    syntax KItem ::= "#pushWorldState"
    syntax KItem ::= "#pushWorldStateAux" "(" Set ")"
    syntax KItem ::= "#pushAccount" "(" Int ")"
 // --------------------------------------------------
    rule <k> #pushWorldState => #pushWorldStateAux(ACCTS) ... </k>
         <activeAccounts> ACCTS </activeAccounts>
         <interimStates> (.List => ListItem(.Set)) ... </interimStates>

    rule #pushWorldStateAux(.Set) => .

    rule #pushWorldStateAux(SetItem(ACCTID) REST) => #pushAccount(ACCTID) ~> #pushWorldStateAux(REST)

    rule <k> #pushAccount(ACCTID) => . ... </k>
         <interimStates> ListItem((.Set => SetItem(@account(ACCTID, BAL, FUN, EVENT, EXTERNAL, STORAGE)))
                                  REST) ... </interimStates>
         <account>
           <acctID>   ACCTID   </acctID>
           <balance>  BAL      </balance>
           <fun>      FUN      </fun>
           <event>    EVENT    </event>
           <external> EXTERNAL </external>
           <storage>  STORAGE  </storage>
         </account>


    syntax KItem ::= "#dropWorldState"
 // ----------------------------------
    rule <k> #dropWorldState => . ... </k>
         <interimStates> (ListItem(_) => .List) ... </interimStates>


///////////////////////////////////////////////////////////////////////////////
// Substate
///////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#pushSubstate"
 // --------------------------------
    rule <k> #pushSubstate => . ... </k>
         <substate> SUBSTATE </substate>
         <substateStack> (.List => ListItem(<substate> SUBSTATE </substate>)) ... </substateStack>


    syntax KItem ::= "#dropSubstate"
 // --------------------------------
    rule <k> #dropSubstate => .K ... </k>
         <substateStack> (ListItem(_) => .List) ... </substateStack>


///////////////////////////////////////////////////////////////////////////////
// Utils
///////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#checkVarName" "(" Int "," Id ")"
 // ---------------------------------------------------
    rule <k> #checkVarName(ACCTID, VARNAME)
            => #If notBool #isVarNameValid(VARNAME)
                 #Then @staticException("Variable name invalid or reserved: " +String Id2String(VARNAME)) #Endif
            ~> #If VARNAME in_keys(STORAGE)
                 #Then @staticException("Variable name overlaps with globals: " +String Id2String(VARNAME)) #Endif
         ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>


// New Account
// ===========


    syntax KItem ::= "#newAccount" "(" Int ")"
 // ------------------------------------------
    rule <k> #newAccount(ACCTID)
            => @dynamicException("Account: " +String Int2String(ACCTID) +String " already exists.")
         ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <fun>    FUN    </fun>
           ...
         </account>
      requires FUN =/=K .Map

    rule <k> #newAccount(ACCTID) => . ... </k>
         <account>
           <acctID>  ACCTID    </acctID>
           <fun>     .Map      </fun>
           <storage> _ => .Map </storage>
           ...
         </account>

    rule <k> #newAccount(ACCTID) => . ... </k>
         <activeAccounts> ACCTS:Set (.Set => SetItem(ACCTID)) </activeAccounts>
         <accounts>
           (.Bag
          => <account>
               <acctID>   ACCTID </acctID>
               <balance>  0      </balance>
               <fun>      .Map   </fun>
               <event>    .Map   </event>
               <external> .Map   </external>
               <storage>  .Map   </storage>
             </account> )
           ...
         </accounts>
     requires notBool ACCTID in ACCTS


// Memory lookup
// =============


    syntax KItem /*ValRecord*/ ::= "#lookupVar" "(" EvaledVar ")"
 // -------------------------------------------------------------
    rule <k> #lookupVar(@%var(VARNAME)) => VR ... </k>
         <memory> ... VARNAME |-> VR:ValRecord ... </memory>

    rule <k> #lookupVar(@%var(VARNAME))
            => @staticException("Undeclared Variable: " +String Id2String(VARNAME)) ... </k>
         <memory> MEM </memory>
      requires notBool VARNAME in_keys(MEM)

    rule <k> #lookupVar(@%svar(VARNAME)) => VR ... </k>
         <id> ACCTID </id>
          <account>
           <acctID> ACCTID </acctID>
           <storage> ... VARNAME |-> VR:ValRecord ... </storage>
           ...
         </account>

    rule <k> #lookupVar(@%svar(VARNAME))
            => @staticException("Persistent variable undeclared: " +String Id2String(VARNAME)) ... </k>
         <id> ACCTID </id>
          <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires notBool VARNAME in_keys(STORAGE)

    rule #lookupVar(@%subscript(EVAR, EEXPR)) => #lookupSubscript(#lookupVar(EVAR), EEXPR)

    rule #lookupVar(@%attribute(EVAR, FIELDNAME)) => #lookupAttribute(#lookupVar(EVAR), FIELDNAME)


    syntax KItem /*ValRecord*/ ::= "#lookupSubscript" "(" K "," EvaledExpr ")"  [strict(1)]
 // ---------------------------------------------------------------------------------------
    rule #lookupSubscript(@val(@tv(%mapT(KT, VT), VALUE), MUTABLE), KEYEXPR)
        => #lookupMapElem(@val(@tv(%mapT(KT, VT), VALUE), MUTABLE), #baseTypeConvert(KEYEXPR, KT))


    syntax KItem /*ValRecord*/ ::= "#lookupMapElem" "(" ValRecord "," K ")"  [strict(2)]
 // ------------------------------------------------------------------------------------
    rule #lookupMapElem(@val(@tv(%mapT(KT, VT), (KEY |-> VAL:TypedValue) MAPVALUE:Map), MUTABLE), @tv(KT, KEY))
        => @val(VAL, MUTABLE)

    rule #lookupMapElem(@val(@tv(%mapT(KT, VT), MAPVALUE), MUTABLE), @tv(KT, KEY))
        => @val(#defaultTypedValue(VT), MUTABLE)
      requires notBool KEY in_keys(MAPVALUE)


    syntax KItem /*ValRecord*/ ::= "#lookupAttribute" "(" K "," Id ")"
 // ------------------------------------------------------------------



// Data Range Checking
// ===================


    syntax KItem ::= "#checkInRangeNum" "(" Int ")"
 // -----------------------------------------------
    rule #checkInRangeNum256(VALUE)
        => #If notBool(VALUE >=Int @minNum andBool VALUE <=Int @maxNum)
             #Then @dynamicException("Number is out of the range of num.") #Endif


    syntax KItem ::= "#checkInRangeNum256" "(" Int ")"
 // --------------------------------------------------
    rule #checkInRangeNum256(VALUE)
        => #If notBool(VALUE >=Int 0 andBool VALUE <=Int @maxNum256)
             #Then @dynamicException("Number is out of the range of num256.") #Endif


// Size of List
// ============

    syntax Int ::= "#numOfParams"    "(" Params ")"          [function]
    syntax Int ::= "#numOfParamsAux" "(" Params "," Int ")"  [function]
 // -------------------------------------------------------------------
    rule #numOfParams(PARAMS) => #numOfParamsAux(PARAMS, 0)

    rule #numOfParamsAux(.Params, NUM) => NUM

    rule #numOfParamsAux((PARAM PARAMS), NUM) => #numOfParamsAux(PARAMS, NUM +Int 1)


    syntax Int ::= "#numOfEvaledExprs"    "(" EvaledExprs ")"          [function]
    syntax Int ::= "#numOfEvaledExprsAux" "(" EvaledExprs "," Int ")"  [function]
 // -----------------------------------------------------------------------------
    rule #numOfEvaledExprs(EEXPRS) => #numOfEvaledExprsAux(EEXPRS, 0)

    rule #numOfEvaledExprsAux(.EvaledExprs, NUM) => NUM

    rule #numOfEvaledExprsAux((EEXPR EEXPRS), NUM) => #numOfEvaledExprsAux(EEXPRS, NUM +Int 1)


endmodule
