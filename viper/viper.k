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
    rule <k> #newAccount(ACCT) => . ... </k>
         <accounts>
           (.Bag
          => <account>
               <acctID>  ACCT </acctID>
               <balance> 0    </balance>
               <code>
                 <funDef>      .Map </funDef>
                 <eventSig>    .Map </eventSig>
                 <externalSig> .Map </externalSig>
               </code>
               <storage> .Map </storage>
             </account> )
           ...
         </accounts>


// JSON
// ====


    syntax JSONList ::= List{JSON,","}
    syntax JSONKey  ::= String | Int
    syntax JSON     ::= String
                      | JSONKey ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"

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


// Simulation
// ==========


    syntax Simulation ::= ".Simulation"
                        | SimulationCommand Simulation
 // ------------------------------------------------------------
    rule .Simulation => .

    rule SC:SimulationCommand SIM:Simulation => SC ~> SIM


    syntax SimulationCommand ::= "load" "account" ":" JSON
 // ------------------------------------------------------
    rule load account : { (ACCTID:String) : CONTENT }
        => #newAccount(#parseAddr(ACCTID))
        ~> load account : { #parseAddr(ACCTID) : CONTENT }

    rule load account : { (ACCTID:Int) : { KEY : VALUE , REST } }
        => load account : { ACCTID : { KEY : VALUE } }
        ~> load account : { ACCTID : { REST } }
      requires REST =/=K .JSONList

    rule load account : { (ACCTID:Int) : { "balance" : ((VAL:String) => #parseWord(VAL)) } }

    rule <k> load account : { (ACCTID:Int) : { "balance" : (BAL:Int) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> _ => BAL </balance>
           ...
         </account>


    syntax SimulationCommand ::= "load" "code" ":" JSON
 // ---------------------------------------------------
    rule load code : { (ACCTID:String) : { CONTENT } }
        => load code : { #parseAddr(ACCTID) : { #sortJSONList(CONTENT) } }

    rule load code : { (ACCTID:Int) : { "arguments" : [ ARGS ], "code" : (CODE:Pgm) } }
        => #loadCode(CODE, #toExprs(ARGS)) ~> #storeCode(ACCTID)

    rule load code : { (ACCTID:Int) : { "code" : (CODE:Pgm) } }
        => #loadCode(CODE, .Exprs) ~> #storeCode(ACCTID)


    syntax Exprs ::= "#toExprs" "(" JSONList ")"  [function]
 // -----------------------------------------------------------
    rule #toExprs(.JSONList) => .Exprs

    rule #toExprs(EXPR:Expr , EXPRS) => EXPR #toExprs(EXPRS)


    syntax KItem  ::= "#storeCode" "(" Int ")"
 // ------------------------------------------


endmodule
