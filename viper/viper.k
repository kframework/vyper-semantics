require "../common/viper-abstract-syntax.k"
require "viper-core.k"
require "domains.k"


module VIPER
    imports VIPER-ABSTRACT-SYNTAX
    imports VIPER-CORE-SEMANTICS


    syntax Int ::= "pow160"  [function]
 // -----------------------------------
    rule pow160 => 2 ^Int 160


// Address
// =======


    syntax Int ::= "#addr" "(" Int ")"  [function]
 // ----------------------------------------------
    rule #addr(W) => W modInt pow160


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


    syntax Int ::= "#parseAddr" "(" String ")"  [function]
 // ------------------------------------------------------
    rule #parseAddr(S) => #addr(#parseHexWord(S))


// Account
// =======


    syntax KItem ::= "#newAccount" "(" Int ")"
 // ------------------------------------------
    rule <k> #newAccount(ACCTID) => . ... </k>
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


// JSON
// ====


    syntax JSONList ::= List{JSON,","}  [klabel(JSONList)]
    syntax JSONKey  ::= String | Int
    syntax JSON     ::= String
                      | JSONKey ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"

    // extend JSONKey and JSON to provide a "pretti-fication" to the nicer input form
    syntax JSONKey ::= Id

    syntax JSON ::= Pgm | Expr | ValRecord | Map

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
 // ---------------------------------------------
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

    rule #loadAccount { (ACCTID:Int) : { "code" : { "arguments" : [ ARGS ], "source" : (CODE:Pgm) } } }
        => #loadCodeAndExecInit(ACCTID, CODE, #toExprs(ARGS))

    rule #loadAccount { (ACCTID:Int) : { "code" : { "source" : (CODE:Pgm) } } }
        => #loadCode(ACCTID, CODE)


    // Load account - storage
    syntax KItem ::= "#loadAccountStorage" "(" Int "," JSONList ")"
 // ---------------------------------------------------------------
    rule #loadAccount { (ACCTID:Int) : { "storage" : { STORAGE:JSONList } } }
        => #loadAccountStorage(ACCTID, STORAGE)


    rule #loadAccountStorage(ACCTID, .JSONList) => .

    rule <k> #loadAccountStorage(ACCTID, ((KEY : VALUE), REST))
            => #loadAccountStorage(ACCTID, REST)
         ... </k>
         <accounts>
           <account>
             <acctID> ACCTID </acctID>
             <storage> ... (KEY |-> (OLD => VALUE)) ... </storage>
             ...
           </account>
           ...
         </accounts>


// Command - exec
// ==============



//////////////////////////////////////////////////////////////////////////////
// Utils
//////////////////////////////////////////////////////////////////////////////


    syntax Exprs ::= "#toExprs" "(" JSONList ")"  [function]
 // --------------------------------------------------------
    rule #toExprs(.JSONList) => .Exprs

    rule #toExprs(EXPR:Expr , EXPRS) => EXPR #toExprs(EXPRS)


endmodule
