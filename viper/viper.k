require "../common/viper-abstract-syntax.k"
require "viper-core.k"
require "viper-verification.k"
require "domains.k"


module VIPER
    imports VIPER-ABSTRACT-SYNTAX
    imports VIPER-CORE-SEMANTICS
    imports VIPER-VERIFICATION


// JSON
// ====


    syntax JSONList ::= List{JSON,","}  [klabel(JSONList)]
    syntax JSONKey  ::= String | Int | Var
    syntax JSON     ::= String
                      | JSONKey ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"

    // extend JSONKey and JSON to provide a "pretti-fication" to the nicer input form
    syntax JSONKey ::= Id

    syntax JSON ::= Pgm | Expr

    syntax JSONList ::= #sortJSONList ( JSONList )            [function]
                      | #sortJSONList ( JSONList , JSONList ) [function, klabel(#sortJSONListAux)]
 // ----------------------------------------------------------------------------------------------
    rule #sortJSONList(JS) => #sortJSONList(JS, .JSONList)

    rule #sortJSONList(.JSONList, LS)            => LS

    rule #sortJSONList(((KEY : VAL) , REST), LS) => #insertJSONKey((KEY : VAL), #sortJSONList(REST, LS))


    syntax JSONList ::= #insertJSONKey ( JSON , JSONList ) [function]
 // -----------------------------------------------------------------
    rule #insertJSONKey( JS , .JSONList ) => JS , .JSONList

    rule #insertJSONKey( (KEY : VAL) , ((KEY' : VAL') , REST) ) => (KEY : VAL)   , (KEY' : VAL')              , REST
      requires KEY <String KEY'

    rule #insertJSONKey( (KEY : VAL) , ((KEY' : VAL') , REST) ) => (KEY' : VAL') , #insertJSONKey((KEY : VAL) , REST)
      requires KEY >=String KEY'

    syntax Bool ::= #isSorted ( JSONList ) [function]
 // -------------------------------------------------
    rule #isSorted( .JSONList ) => true

    rule #isSorted( KEY : _ )   => true

    rule #isSorted( (KEY : _) , (KEY' : VAL) , REST ) => KEY <=String KEY' andThenBool #isSorted((KEY' : VAL) , REST)


//////////////////////////////////////////////////////////////////////////////
// Simulation
//////////////////////////////////////////////////////////////////////////////


    syntax Simulation ::= ".Simulation"
                        | SimulationCommand Simulation
 // ------------------------------------------------------------
    rule .Simulation => .

    rule SC:SimulationCommand SIM:Simulation => SC ~> SIM


// Command - Load
// ==============


    syntax SimulationCommand ::= "load" JSON
 // ----------------------------------------
    rule load DATA : { .JSONList } => .

    rule load DATA : { KEY : VALUE , REST }
        => load DATA : { KEY : VALUE } ~> load DATA : { REST }
      requires REST =/=K .JSONList


    // Load account
    // CONTENT is sorted here so that key "storage" comes after key "code"
    syntax KItem ::= "#loadAccount" JSON
 // ------------------------------------
    rule load "account" : { (ACCTSTR:String) : { CONTENT } }
        => #newAccount(#parseAddr(ACCTSTR))
        ~> #loadAccount { #parseAddr(ACCTSTR) : { #sortJSONList(CONTENT) } }

    rule #loadAccount { (ACCTID:Int) : { KEY : VALUE , REST } }
        => #loadAccount { ACCTID : { KEY : VALUE } }
        ~> #loadAccount { ACCTID : { REST } }
      requires REST =/=K .JSONList

    // Load account - balance
    rule #loadAccount { (ACCTID:Int) : { "balance" : ((VAL:String) => #parseWord(VAL)) } }

    rule <k> #loadAccount { (ACCTID:Int) : { "balance" : (BAL:Int) } } => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <balance> _ => BAL </balance>
           ...
         </account>

    // Load account - code
    rule #loadAccount { (ACCTID:Int) : { "code" : { CONTENT } } }
        => #loadAccount { ACCTID : { "code" : { #sortJSONList(CONTENT) } } }
      requires notBool #isSorted(CONTENT)

    rule #loadAccount { (ACCTID:Int) : { "code" : { .JSONList } } } => .

    rule #loadAccount { (ACCTID:Int) : { "code" : { "args" : [ ARGS ], "source" : (CODE:Pgm) } } }
        => #loadProgramAndInit(ACCTID, CODE, #toExprs(ARGS))

    rule #loadAccount { (ACCTID:Int) : { "code" : { "source" : (CODE:Pgm) } } }
        => #loadProgramAndInit(ACCTID, CODE)


    // Load account - storage
    syntax KItem ::= "#loadStorage" "(" JSONList ")"
 // ------------------------------------------------
    rule <k> #loadAccount { (ACCTID:Int) : { "storage" : { STORAGES:JSONList } } }
            => #loadStorage(STORAGES) ~> #clearVyperState ... </k>
         <id> _ => ACCTID </id>

    rule #loadStorage(.JSONList) => .

    rule #loadStorage((KEY : VALUE), REST)
        => #evalStmt(%assign(KEY, VALUE)) ~> #loadStorage(REST)


// Command - Exec
// ==============


    syntax SimulationCommand ::= "exec" JSON
 // ----------------------------------------
    rule exec { "from" : (ACCTFROM:String), "to" : (ACCTTO:String), "value" : (VALUE:String),
                "function" : (FUNCNAME:String), "args" : [ ARGS ] }
        => @%exec(#parseHexWord(ACCTFROM),
                  #parseHexWord(ACCTTO),
                  #parseWord(VALUE),
                  String2Id(FUNCNAME),
                  #toExprs(ARGS))


    syntax Expr  ::= "@%exec" "(" Int "," Int "," Int "," Id "," Exprs ")"
    syntax KItem ::= "#execAux" "(" Int "," Int "," Int "," Id "," K ")"  [strict(5)]
 // --------------------------------------------------------------------------------
    rule @%exec(ACCTFROM, ACCTTO, VALUE, FUNCNAME, ARGS)
        => #execAux(ACCTFROM, ACCTTO, VALUE, FUNCNAME, #evalExprs(ARGS, .EvaledExprs))

    rule #execAux(ACCTFROM, ACCTTO, VALUE, FUNCNAME, EARGS:EvaledExprs)
        => #call(ACCTFROM, ACCTTO, VALUE, FUNCNAME, EARGS)


//////////////////////////////////////////////////////////////////////////////
// Utils
//////////////////////////////////////////////////////////////////////////////


    syntax Exprs ::= "#toExprs" "(" JSONList ")"  [function]
 // --------------------------------------------------------
    rule #toExprs(.JSONList) => .Exprs

    rule #toExprs(EXPR:Expr , EXPRS) => EXPR #toExprs(EXPRS)


endmodule
