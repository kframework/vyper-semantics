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
        <order>    0     </order>

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
   syntax EvaledVar ::= "@evar" "(" Var ")"

   syntax Var ::= "#subscript" "(" Var "," EvaledExpr ")"


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


    syntax KItem ::= "#loadCode" "(" Int "," Pgm ")"
 // ------------------------------------------------
    rule <k> #loadCode(ACCTID, %pgm(ES, GS, DEFS))
            => ES ~> GS ~> (DEFS ++Def #mkPublicGetters(GS, .Defs)) ~> #clearVyperState
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
            => @staticException("Duplicate event name: " +String Id2String(EVENTNAME))
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
             #then @staticException("Argument name invalid or reserved: " +String Id2String(NAME)) #fi
        ~> #if #isInIds(NAME, NAMES)
             #then @staticException("Duplicate function argument name: " +String Id2String(NAME)) #fi


    syntax KItem ::= "#checkEventParamType" "(" Type ")"
 // ----------------------------------------------------
    rule #checkEventParamType(%bytesT(N)) => .
      requires N <=Int 32

    rule #checkEventParamType(%bytesT(N)) => #exception("Can only log a maximum of 32 bytes at a time.")
      requires N >Int 32

    rule #checkEventParamType(T) => .
      requires notBool isByteArrayType(T)


    syntax KItem ::= "#addEvent" "(" Id "," K /*EventParams*/ ")"  [strict(2)]
 // --------------------------------------------------------------------------
    rule <k> #addEvent(EVENTNAME, EPARAMS:EventParams) => . ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <event> EVENTS => EVENTS[EVENTNAME <- @event(EVENTNAME, EPARAMS)] </event>
           ...
         </account>


    syntax KItem /*EventParams*/ ::= "#parseTypeForEventParams" "(" EventParams "," EventParams ")"
 // -----------------------------------------------------------------------------------------------
    rule #parseTypeForEventParams(.EventParams, RESULT) => RESULT

    rule #parseTypeForEventParams(%eparam(NAME, T, ISTOPIC) EPARAMS, RESULT)
        => #parseTypeForEventParam(NAME, #parseType(T, true), ISTOPIC)
        ~> #parseTypeForEventParams(EPARAMS, RESULT)

    rule EPARAM:EventParam ~> #parseTypeForEventParams(EPARAMS, RESULT)
        => #parseTypeForEventParams(EPARAMS, RESULT ++Eparam (EPARAM .EventParams))


    syntax KItem ::= "#parseTypeForEventParam" "(" Id "," K /*Type*/ "," Bool ")"  [strict(2)]
 // -------------------------------------------------------------------------------------------
    rule #parseTypeForEventParam(NAME, T:Type, TOPIC) => %eparam(NAME, T, TOPIC)


// Global Declarations
// ===================


    rule .Globals => .

    rule G:Global GS:Globals => G ~> GS

    rule <k> %svdecl(VARNAME, T, _)
            => #if notBool #isVarNameValid(VARNAME)
                #then @staticException("Variable name invalid or reserved: " +String Id2String(VARNAME)) #fi
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
            => @staticException("Cannot declare a persistent variable twice! " +String Id2String(VARNAME))
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires VARNAME in_keys(STORAGE)


    syntax KItem ::= "#addGlobal" "(" Id "," K /*Type*/ ")"  [strict(2)]
 // --------------------------------------------------------------------
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


    syntax KItem ::= "#addFunc" "(" Id "," Params "," Type "," Stmts "," Bool "," Bool "," Bool "," Bool "," Int ")"
 // ----------------------------------------------------------------------------------------------------------------
    rule <k> #addFunc(FUNCNAME, PARAMS, RT, FUNCBODY, CONSTANT, PAYABLE, PRIVATE, PUBLIC, ORDER)
            => #checkFuncParams(PARAMS, .Ids)
            ~> #checkPrivatePublicMECE(PRIVATE, PUBLIC)
            ~> #addFuncAux(FUNCNAME,
                           #parseTypeForParams(PARAMS, .Params),
                           #parseType(RT, true),
                           FUNCBODY,
                           CONSTANT, PAYABLE, PRIVATE, ORDER)
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <fun> FUNCS </fun>
           <event> EVENTS </event>
           ...
         </account>
      requires notBool(FUNCNAME in_keys(FUNCS)) andBool notBool(FUNCNAME in_keys(EVENTS))

    rule <k> #addFunc(FUNCNAME, PARAMS, RT, FUNCBODY, CONSTANT, PAYABLE, PRIVATE, PUBLIC, ORDER)
            => @staticException("Duplicate event or function name: " +String Id2String(FUNCNAME))
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
        => #checkVarName(NAME)
        ~> #if #isInIds(NAME, NAMES)
             #then @staticException("Duplicate function argument name: " +String Id2String(NAME)) #fi


    syntax KItem ::= "#checkPrivatePublicMECE" "(" Bool /*private?*/ "," Bool /*public?*/ ")"
 // -----------------------------------------------------------------------------------------
    rule #checkPrivatePublicMECE(PRIVATE, PUBLIC)
        => #if PRIVATE ==K true andBool PUBLIC ==K true
             #then @staticException("Cannot use public and private decorators on the same function.") #fi
        ~> #if PRIVATE ==K false andBool PUBLIC ==K false
             #then @staticException("Function visibility must be declared (@public or @private).") #fi


    syntax KItem ::= "#addFuncAux" "(" Id "," K /*Params*/ "," K /*Type*/ "," Stmts "," Bool "," Bool "," Bool "," Int ")"  [strict(2, 3)]
 // --------------------------------------------------------------------------------------------------------------------------------------
    rule <k> #addFuncAux(FUNCNAME, PARAMS:Params, RT:Type, FUNCBODY, CONSTANT, PAYABLE, PRIVATE, ORDER)
            => . ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <fun> FUNCS
                => FUNCS[FUNCNAME <- @func(FUNCNAME, PARAMS, RT, FUNCBODY, CONSTANT, PAYABLE, PRIVATE, ORDER)] </fun>
           ...
         </account>


    syntax KItem /*Params*/ ::= "#parseTypeForParams" "(" Params "," Params ")"
 // ---------------------------------------------------------------------------
    rule #parseTypeForParams(.Params, RESULT) => RESULT

    rule #parseTypeForParams(%param(NAME, T) PARAMS, RESULT)
        => #parseTypeForParam(NAME, #parseType(T, true))
        ~> #parseTypeForParams(PARAMS, RESULT)

    rule PARAM:Param ~> #parseTypeForParams(PARAMS, RESULT)
        => #parseTypeForParams(PARAMS, RESULT ++Param (PARAM .Params))


    syntax KItem ::= "#parseTypeForParam"  "(" Id "," K /*Type*/ ")"  [strict(2)]
 // -----------------------------------------------------------------------------
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


    syntax KItem ::= "#newVar" "(" Id "," K /*Type*/ ")"  [strict(2)]
    syntax KItem ::= "#newVarAux" "(" Id "," Type ")"
 // -----------------------------------------------------------------
    rule #newVar(VARNAME, T) => #checkVarName(VARNAME) ~> #newVarAux(VARNAME, T)

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


    syntax KItem ::= "#annassign" "(" Id "," K /*Type*/ "," K /*EvaledExpr*/ ")"  [seqstrict(2, 3)]
 // -----------------------------------------------------------------------------------------------
    rule #annassign(VARNAME, VARTYPE:Type, @ee(EXPRTYPE, VALUE, LITERAL))
        => #newVar(VARNAME, VARTYPE)
        ~> #assign(@ee(EXPRTYPE, VALUE, LITERAL), @evar(%var(VARNAME)))


// Assignment
// ----------


    rule #evalStmt(%assign(VAR, EXPR)) => #assign(#evalExpr(EXPR), #evalVar(VAR))


    syntax KItem ::= "#assign" "(" K /*EvaledExpr*/ "," K /*EvaledVar*/ ")"  [seqstrict]
    syntax KItem ::= "#assignAux" "(" EvaledExpr "," Var "," K /*ValRecord*/ ")"  [strict(3)]
 // -----------------------------------------------------------------------------------------
    rule #assign(EEXPR:EvaledExpr, @evar(VAR))
        => #assignAux(EEXPR, VAR, #lookupVar(VAR))

    rule #assignAux(EEXPR, VAR, @val(_, false))
        => @staticException("Cannot modify function argument.")

    rule #assignAux(EEXPR, VAR, @val(@tv(OLDTYPE, _), true))
        => #assignHelper(VAR, #baseTypeConvert(EEXPR, OLDTYPE))
      requires isBaseType(OLDTYPE)


    syntax KItem ::= "#assignHelper" "(" Var "," K ")"  [strict(2)]
 // ------------------------------------------------------------
    rule <k> #assignHelper(%var(VARNAME), TVNEW:TypedValue) => . ... </k>
         <memory> MEM => MEM[VARNAME <- @val(TVNEW, true)] </memory>

    rule <k> #assignHelper(%svar(VARNAME), TVNEW:TypedValue) => . ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE => STORAGE[VARNAME <- @val(TVNEW, true)] </storage>
           ...
         </account>

    rule #assignHelper(#subscript(VAR, EEXPR), TV)
        => #assignHelper(VAR, #updateMap(#lookupVar(VAR), EEXPR, TV))


    syntax KItem /*TypedValue*/ ::= "#updateMap" "(" K /*ValRecord*/ "," K "," TypedValue ")"  [strict(1)]
 // ------------------------------------------------------------------------------------------------------
    rule #updateMap(@val(@tv(%mapT(KT, VT), MAPVALUE:Map), _), EEXPR:EvaledExpr, TV)
        => #updateMapAux(@tv(%mapT(KT, VT), MAPVALUE), #baseTypeConvert(EEXPR, KT), TV)


    syntax KItem /*TypedValue*/ ::= "#updateMapAux" "(" TypedValue "," K /*TypedValue*/ "," TypedValue ")"  [strict(2)]
 // -------------------------------------------------------------------------------------------------------------------
    rule #updateMapAux(@tv(T, MAP:Map), @tv(KT, KEY), TV) => @tv(T, MAP[KEY <- TV])


    syntax KItem /*EvaledExpr*/ ::= "#getAssignTarget" "(" Var ")"
 // --------------------------------------------------------------
    rule <k> #getAssignTarget(%var(VARNAME))
            => #if %var(VARNAME) in FORVARS
                 #then @staticException("Altering iterator which is in use!") #fi
            ~> #if %var(VARNAME) in INLOOP
                 #then @staticException("Altering list which is being iterated!") #fi
            ~> #evalVar(%var(VARNAME))
         ... </k>
         <forvar> FORVARS </forvar>
         <inLoop> INLOOP </inLoop>

    rule <k> #getAssignTarget(%svar(VARNAME))
            => #if CONSTANT ==K true
                 #then @staticException("Cannot modify storage inside a constant function") #fi
            ~> #if %var(VARNAME) in INLOOP
                 #then @staticException("Altering list which is being iterated!") #fi
            ~> #evalVar(%svar(VARNAME))
         ... </k>
         <constant> CONSTANT </constant>
         <inLoop> INLOOP </inLoop>

    rule <k> #getAssignTarget(%subscript(VAR, INDEX))
            => #if VAR in INLOOP
                 #then @staticException("Altering list which is being iterated!") #fi
            ~> #evalVar(%subscript(VAR, INDEX))
         ... </k>
         <inLoop> INLOOP </inLoop>

    rule #getAssignTarget(%attribute(VAR, FIELDNAME)) => #evalVar(%attribute(VAR, FIELDNAME))


    syntax KItem /*EvaledVar*/ ::= "#evalVar" "(" Var ")"
    syntax KItem /*EvaledVar*/ ::= "#evalSubscriptVar" "(" K "," K ")"  [seqstrict]
    syntax KItem /*EvaledVar*/ ::= "#evalAttributeVar" "(" K "," Id ")"  [strict(1)]
 // --------------------------------------------------------------------------------
    rule #evalVar(%var(VARNAME)) => @evar(%var(VARNAME))

    rule #evalVar(%svar(VARNAME)) => @evar(%svar(VARNAME))

    rule #evalVar(%subscript(VAR, EXPR)) => #evalSubscriptVar(#evalVar(VAR), #evalExpr(EXPR))

    rule #evalVar(%attribute(VAR, FIELDNAME)) => #evalAttributeVar(#evalVar(VAR), FIELDNAME)

    rule #evalSubscriptVar(@evar(VAR), EEXPR:EvaledExpr) => @evar(#subscript(VAR, EEXPR))

    rule #evalAttributeVar(@evar(VAR), FIELDNAME) => @evar(#attribute(VAR, FIELDNAME))


// Return
// ------

    rule #evalStmt(%return(EXPR)) => #return(#evalExpr(EXPR))


    syntax KItem ::= "#return"
 // --------------------------


    syntax KItem ::= "#return" "(" K ")"  [strict]
 // ----------------------------------------------


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
           <fun> ... FUNCNAME |-> FUNCRECORD ... </fun>
           ...
         </account>

    rule <k> #call(ACCTFROM, ACCTTO, VALUE, FUNCNAME, EARGS)
            => @dynamicException("Function " +String Id2String(FUNCNAME) +String "not declared yet.")
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
            ~> #mkCall(ACCTFROM, ACCTTO, VALUE, FUNCRECORD, EARGS)
         ... </k>
         <order> ORDER </order>


    syntax KItem ::= "#checkFuncOrder" "(" Int "," Int "," Int "," FuncRecord ")"
 // -----------------------------------------------------------------------------
    rule #checkFuncOrder(ACCTFROM, FROMORDER, ACCTTO, @func(FUNCNAME, _, _, _, _, _, _, TOORDER))
        => #if (ACCTFROM ==K ACCTTO) andBool (FROMORDER <Int TOORDER)
             #then @staticException("Function " +String Id2String(FUNCNAME) +String "is called before being declared.") #fi


    syntax State ::= "@state" "(" Int  "," K "," Map "," List "," Set "," Set "," Bool "," Type "," Int "," Int "," Int ")"
 // -----------------------------------------------------------------------------------------------------------------------


    syntax KItem ::= "#pushCallStack" "(" K ")"
 // -------------------------------------------
    rule <k> #pushCallStack(RESTPGM) => . ... </k>
         <callStack> (.List
                    => ListItem(@state(ACCT, RESTPGM, MEM, MEMSTACK, FORVAR, INLOOP, CONSTANT, RT, ORDER, CR, CV)))
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
         <id>        ACCT     </id>
         <caller>    CR       </caller>
         <callValue> CV       </callValue>


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


    syntax KItem ::= "#pushSubstate"
 // --------------------------------
    rule <k> #pushSubstate => . ... </k>
         <substate> SUBSTATE </substate>
         <substateStack> (.List => ListItem(<substate> SUBSTATE </substate>)) ... </substateStack>


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
            ~> #if #numOfParams(PARAMS) =/=Int #numOfEvaledExprs(EARGS)
                 #then @staticException("# of args doesn't match # of params in function" +String Id2String(FUNCNAME)) #fi
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

    rule <k> #checkFuncPrivate(true) => . </k>
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
    syntax KItem /*TypedValue*/ ::= "#asNum256" "(" K ")"  [strict]
 // ---------------------------------------------------------------
   rule #evalExpr(%as_num256(EXPR)) => #asNum256(#evalExpr(EXPR))

   rule #asNum256(@ee(T, VALUE, _))
       => #if notBool(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %address))
            #then @staticException("Function arg type does not match expected type.") #fi
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


    syntax KItem /*Type*/ ::= "#parseType" "(" Type "," Bool /*in memory?*/ ")"
 // ---------------------------------------------------------------------------
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
             #then @staticException("Bad byte array length: " +String Int2String(N)) #fi
        ~> %bytesT(N)

    rule #parseType(%listT(SUBTYPE, N), INMEMORY)
        => #parseListType(#parseType(SUBTYPE, INMEMORY), N)

    rule #parseType(%mapT(KT, VT), true)
        => @staticException("No mappings allowed for in-memory types, only fixed-size arrays")

    rule #parseType(%mapT(KT, VT), false)
        => #if isBaseType(KT) orBool isByteArrayType(KT)
             #then #parseMapType(#parseType(KT, false), #parseType(VT, false))
             #else @staticException("Mapping keys must be base or bytes types") #fi

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


    syntax KItem /*Type*/ ::= "#parseListType" "(" K /*Type*/ "," Int ")"  [strict(1)]
 // ----------------------------------------------------------------------------------
    rule #parseListType(T, N) => %listT(T, N)


    syntax KItem /*Type*/ ::= "#parseMapType" "(" K /*KT*/ "," K /*VT*/ ")"  [seqstrict]
 // ------------------------------------------------------------------------------------
    rule #parseMapType(KT, VT) => %mapT(KT, VT)


    syntax KItem /*Type*/ ::= "#parseStructType" "(" AnnVars "," Bool "," Ids "," AnnVars ")"
 // -----------------------------------------------------------------------------------------
    rule #parseStructType(.AnnVars, _, _, ANNVARS) => %structT(ANNVARS)

    rule #parseStructType(%annvar(FIELDNAME, T) ANNVARS, INMEMORY, FIELDNAMES, RESULT)
        => #if notBool #isVarNameValid(FIELDNAME)
             #then @staticException("Invalid member variable for struct.") #fi
        ~> #if #isInIds(FIELDNAME, FIELDNAMES)
             #then @staticException("Member variable duplicated: " +String Id2String(FIELDNAME)) #fi
        ~> #parseTypeForField(FIELDNAME, #parseType(T, INMEMORY))
        ~> #parseStructType(ANNVARS, INMEMORY, FIELDNAMES, RESULT)

    rule %annvar(FIELDNAME, T) ~> #parseStructType(ANNVARS, INMEM, FIELDNAMES, RESULT)
        => #parseStructType(ANNVARS, INMEM, FIELDNAMES ++Id (FIELDNAME .Ids), RESULT ++Annvar (%annvar(FIELDNAME, T) .AnnVars))


    syntax KItem ::= "#parseTypeForField" "(" Id "," K /*Type*/ ")"  [strict(2)]
 // ----------------------------------------------------------------------------
    rule #parseTypeForField(FIELDNAME, T:Type) => %annvar(FIELDNAME, T)


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



// Utils
// =====


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
        => #if notBool #areUnitsCompatible(FROMTYPE, LITERAL, TOTYPE)
             #then @staticException("Base type conversion unavailable due to incompatible units") #fi
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
// Utils
///////////////////////////////////////////////////////////////////////////////


    syntax KItem ::= "#checkVarName" "(" Id ")"
 // -------------------------------------------
    rule <k> #checkVarName(VARNAME)
            => #if notBool #isVarNameValid(VARNAME)
                 #then @staticException("Variable name invalid or reserved: " +String Id2String(VARNAME)) #fi
            ~> #if VARNAME in_keys(STORAGE)
                 #then @staticException("Variable name overlaps with globals: " +String Id2String(VARNAME)) #fi
         ... </k>
         <id> ACCTID </id>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>


// Address
// =======


    syntax Int ::= "#addr" "(" Int ")"  [function]
 // ----------------------------------------------
    rule #addr(W) => W modInt pow160


    syntax Int ::= "#parseAddr" "(" String ")"  [function]
 // ------------------------------------------------------
    rule #parseAddr(S) => #addr(#parseHexWord(S))


// Account
// =======


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


    syntax KItem /*ValRecord*/ ::= "#lookupVar" "(" Var ")"
 // -------------------------------------------------------
    rule <k> #lookupVar(%var(VARNAME)) => VR ... </k>
         <memory> ... VARNAME |-> VR:ValRecord ... </memory>

    rule <k> #lookupVar(%var(VARNAME))
            => @staticException("Undeclared Variable: " +String Id2String(VARNAME)) ... </k>
         <memory> MEM </memory>
      requires notBool VARNAME in_keys(MEM)

    rule <k> #lookupVar(%svar(VARNAME)) => VR ... </k>
         <id> ACCTID </id>
          <account>
           <acctID> ACCTID </acctID>
           <storage> ... VARNAME |-> VR:ValRecord ... </storage>
           ...
         </account>

    rule <k> #lookupVar(%svar(VARNAME))
            => @staticException("Persistent variable undeclared: " +String Id2String(VARNAME)) ... </k>
         <id> ACCTID </id>
          <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires notBool VARNAME in_keys(STORAGE)

    rule #lookupVar(%subscript(VAR, EXPR)) => #lookupSubscript(#lookupVar(VAR), #evalExpr(EXPR))

    rule #lookupVar(#subscript(VAR, EEXPR)) => #lookupSubscript(#lookupVar(VAR), EEXPR)

    rule #lookupVar(%attribute(VAR, FIELDNAME)) => #lookupAttribute(#lookupVar(VAR), FIELDNAME)


    syntax KItem /*ValRecord*/ ::= "#lookupSubscript" "(" K "," K ")"  [seqstrict]
 // ------------------------------------------------------------------------------
    rule #lookupSubscript(@val(@tv(%mapT(KT, VT), VALUE), MUTABLE), EEXPR:EvaledExpr)
        => #lookupMapElem(@val(@tv(%mapT(KT, VT), VALUE), MUTABLE), #baseTypeConvert(EEXPR, KT))


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
        => #if notBool(VALUE >=Int @minNum andBool VALUE <=Int @maxNum)
             #then @dynamicException("Number is out of the range of num.") #fi


    syntax KItem ::= "#checkInRangeNum256" "(" Int ")"
 // --------------------------------------------------
    rule #checkInRangeNum256(VALUE)
        => #if notBool(VALUE >=Int 0 andBool VALUE <=Int @maxNum256)
             #then @dynamicException("Number is out of the range of num256.") #fi


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
