requires "domains.k"

module VYPER-ABSTRACT-SYNTAX
    imports DOMAINS

    syntax Pgm  ::= "%pgm" "(" Events "," Globals "," Defs "," Contracts ")"
                  | "%pgm" "(" Events "," Globals "," Def /*Init function*/ "," Defs "," Contracts ")"


// Event
// ======


    syntax Event  ::= "%event" "(" Id "," EventParams ")"
    syntax Events ::= List{Event, ""}  [klabel(Events)]

    syntax EventParam  ::= "%eparam" "(" Id "," Type "," Bool /*indexed?*/ ")"
    syntax EventParams ::= List{EventParam, ""}  [klabel(EventParams)]


// Global
// =======


    syntax Global  ::= "%svdecl" "(" Id "," Type "," Visibility ")"
    syntax Globals ::= List{Global, ""}  [klabel(Globals)]

    syntax Visibility  ::= "%public" | "%private"


// Function Definition
// ===================


    syntax Def  ::= "%fdecl" "(" Decorators "," Id "," Params "," Type "," Stmts ")"
    syntax Defs ::= List{Def, ""}  [klabel(Defs)]

    syntax Decorator  ::= "%@constant" | "%@payable" | "%@private" | "%@public"
    syntax Decorators ::= List{Decorator, ""}  [klabel(Decorators)]

    syntax Param  ::= "%param" "(" Id "," Type ")"
    syntax Params ::= List{Param, ""}  [klabel(Params)]


// Contracts
// ======

           /*Syntax is that of class declaration:

              class Foo():
                  def foo(arg1: num) -> num: pass
           */
    syntax Contract ::= "%contract" "(" Id   //contract name
                                    "," Defs //contract functions
                                    ")"
    syntax Contracts ::= List{Contract, ""}  [klabel(Contracts)]

// Statement
// =========


    syntax Stmt  ::= AnnVar
                   | "%annassign" "(" Id "," Type "," Expr ")"
                   | "%assign"    "(" Var "," Expr ")"
                   | "%augassign" "(" AugAssignOp "," Var "," Expr ")"
                   | "%if"        "(" Expr "," Stmts "," Stmts ")"
                   | "%if"        "(" Expr "," Stmts ")"
                   | "%forrange"  "(" Id "," Int  "," Stmts ")"            // for i in range(rounds)
                   | "%forrange"  "(" Id "," Expr "," Expr  "," Stmts ")"  // for i in range(start, start + rounds)
                   | "%forlist"   "(" Id "," Expr "," Stmts ")"            // for i in list()
                   | "%break"
                   | "%pass"
                   | "%return"
                   | "%return"    "(" Expr ")"
                   | "%assert"    "(" Expr ")"
                   | "%throw"
                   | "%log"       "(" Id "," Exprs ")"
                   | "%stmtexpr"  "(" Expr ")"
                   // stmt dispatch table
                   | "%send"      "(" Expr "," Expr ")"
                   | "%selfdestruct" "(" Expr ")"
                   | "%rawlog"    "(" Expr "," Expr ")"

    syntax Stmts    ::= List{Stmt, ""}  [klabel(Stmts)]

    syntax AnnVar   ::= "%annvar" "(" Id "," Type ")"
                        /*Variable declaration with initializer.
                          Ex:
                            z: int128 = x
                        */
                      | "%annvar" "(" Id "," Type "," Expr ")"

    syntax AnnVars  ::= List{AnnVar, ""}  [klabel(AnnVars)]

    syntax AugAssignOp ::= "+=" | "-=" | "*=" | "/=" | "%="


// Expression
// ==========


    syntax Expr  ::= Const
                   | Var
                   | ListExpr
                   | StructExpr
                   | "%self"
                   | "%binop"     "(" BinOp     "," Expr "," Expr ")"
                   | "%compareop" "(" CompareOp "," Expr "," Expr ")"
                   | "%boolop"    "(" BoolOp    "," Expr "," Expr ")"
                   | "%unaryop"   "(" UnaryOp   "," Expr ")"
                   | "%icall"     "(" Id /*func name*/ "," Exprs ")"  // internal contract call

                      //example: self.token_address.balanceOf(_owner)
                   | "%ecall"     "(" Expr /*address*/ "," Id /*func name*/ "," Exprs ")"  // external contract call

                      /*example: class Foo():...
                                 Foo(arg1).foo(arg2)
                      */
                   | "%ecall"     "(" Id      //contract name
                                  "," Expr    //cotnract address
                                  "," Id      //function name
                                  "," Exprs   //function args
                                  ")"  // external contract call
                   | ReservedExpr
                   | ReservedFunc  // expr dispatch table

    syntax Exprs ::= List{Expr, ""}    [klabel(Exprs)]

    syntax Const  ::= Int
                    | FixedPoint
                    | "%hex"     "(" String ")"
                    | String
                    | Bool
                    | "%None"

    syntax FixedPoint  ::= "%fixed10" "(" Int "," Int ")"  // decimal fixed point value with a precision of 10 decimal places
                                                           // %fixed10(A, B) = A/B and B is a power of 10.

    syntax Var  ::= "%var"  "(" Id ")"
                  | "%svar" "(" Id ")"
                  | SubscriptVar
                  | AttributeVar

    // Var[Expr]: list or map element
    syntax SubscriptVar  ::= "%subscript" "(" Var "," Expr ")"

    // Var.Id: struct field access
    syntax AttributeVar  ::= "%attribute" "(" Var "," Id   ")"

    syntax ListExpr  ::= "%list" "(" Exprs ")"

    syntax StructExpr  ::= "%struct" "(" StructItems ")"

    syntax StructItem  ::= "%item" "(" Id "," Expr ")"
    syntax StructItems ::= List{StructItem, ""}

    syntax BinOp         ::= "+" | "-" | "*" | "/" | "%" | "**"

    syntax CompareOp     ::= "%lt" | "%le" | "%gt" | "%ge" | "%eq" | "%ne" | "%in"

    syntax BoolOp        ::= "%and" | "%or"

    syntax UnaryOp       ::= "%not" | "%neg"


// Type
// ====


    syntax Type  ::= "%void"
                   | BaseType
                   | ByteArrayType
                   | ListType
                   | MappingType
                   | StructType

    syntax BaseType  ::= "%bool"
                       | NumericType | "%num256"  | "%signed256"
                       | "%bytes32"
                       | AddressType

    syntax NumericType  ::= PureNumType
                          | UnitType
                          | CastType

    syntax PureNumType  ::= "%num" | "%decimal"

    syntax UnitType  ::= "%unitT" "(" PureNumType "," Unit "," Bool /*positional*/ ")"
                       | "%timestamp"      | "%timedelta"
                       | "%currency_value" | "%currency1_value" | "%currency2_value" | "%wei_value"

    /*Type cast inside parameter declaration:
          def _num256_to_num(x: num(num256))
      In fact only %castT(%num, %num256) is considered.
    */
    syntax CastType  ::= "%castT" "(" BaseType "," BaseType ")"

    syntax AddressType  ::= "%address"
                          | "%contractT" "(" Id ")"

    syntax Unit  ::= BaseUnit
                   | "%umul" "(" Unit "," Unit ")"
                   | "%udiv" "(" Unit "," Unit ")"
                   | "%upow" "(" BaseUnit "," Int ")"

    syntax BaseUnit  ::= "%wei" | "%currency" | "%currency1" | "%currency2"
                       | "%sec" | "%m"        | "%kg"

    syntax ByteArrayType  ::= "%bytesT" "(" Int ")"

    syntax ListType  ::= "%listT" "(" Type "," Int ")"

    syntax MappingType  ::= "%mapT" "(" Type "," Type ")" // keyType, valueType

    syntax StructType  ::= "%structT" "(" AnnVars ")"


// Reserved
// ========


    syntax Id ::= ReservedWord

    syntax ReservedWord  ::= "__init__" [token]
                           | "wei"  [token]
                           | "kwei" [token] | "ada" [token] | "lovelace" [token]
                           | "babbage" [token]
                           | "shannon" [token] | "gwei" [token]
                           | "szabo"   [token]
                           | "finney"  [token]
                           | "ether"   [token]

    syntax ReservedExpr  ::= "%balance" "(" Expr ")" | "%codesize" "(" Expr ")" | "%is_contract" "(" Expr ")"
                           | "%msg.sender" | "%msg.value" | "%msg.gas"
                           | "%block.difficulty" | "%block.timestamp" | "%block.coinbase" | "%block.number" | "%block.prevhash"
                           | "%tx.origin"

    syntax ReservedFunc  ::= "%floor"               "(" Expr ")"
                           | "%decimal"             "(" Expr ")"
                           | "%as_unitless_number"  "(" Expr ")"
                           | "%convert"             "(" Expr ","  //target
                                                        String    //new type
                                                    ")"
                           | "%as_num256"           "(" Expr ")"  //todo obsolete, replaced by %convert
                           | "%slice"               "(" Expr "," Expr "," Expr ")"
                           | "%len"                 "(" Expr ")"
                           | "%concat"              "(" Exprs ")"                      //byte arrays concatenation
                           | "%keccak256"           "(" Expr ")"
                           | "%method_id"           "(" Expr ")"
                           | "%ecrecover"           "(" Expr "," Expr "," Expr "," Expr ")"
                           | "%ecadd"               "(" Expr "," Expr ")"
                           | "%ecmul"               "(" Expr "," Expr ")"
                           | "%extract32"           "(" Expr "," Expr "," Type ")"
                           | "%bytes_to_num"        "(" Expr ")"
                           | "%as_wei_value"        "(" Expr "," Id   ")"
                           | "%raw_call"            "(" Expr    // address
                                                    "," Expr    // data: Bytes
                                                    "," Expr    // outsize: num_literal
                                                    "," Expr    // gas: int128
                                                    "," Expr    // value: int128 optional
                                                    ")"
                           | "%RLPlist"             "(" Expr "," Expr ")"
                           | "%blockhash"           "(" Expr ")"
                           | "%bitwise_and"         "(" Expr "," Expr ")"
                           | "%bitwise_or"          "(" Expr "," Expr ")"
                           | "%bitwise_xor"         "(" Expr "," Expr ")"
                           | "%bitwise_not"         "(" Expr ")"
                           | "%uint256_add"         "(" Expr "," Expr ")"
                           | "%uint256_sub"         "(" Expr "," Expr ")"
                           | "%uint256_mul"         "(" Expr "," Expr ")"
                           | "%uint256_div"         "(" Expr "," Expr ")"
                           | "%uint256_exp"         "(" Expr "," Expr ")"
                           | "%uint256_mod"         "(" Expr "," Expr ")"
                           | "%uint256_addmod"      "(" Expr "," Expr "," Expr ")"
                           | "%uint256_mulmod"      "(" Expr "," Expr "," Expr ")"
                           | "%uint256_gt"          "(" Expr "," Expr ")"
                           | "%uint256_ge"          "(" Expr "," Expr ")"
                           | "%uint256_lt"          "(" Expr "," Expr ")"
                           | "%uint256_le"          "(" Expr "," Expr ")"
                           | "%shift"               "(" Expr "," Expr ")"
                        // | "%create_with_code_of" "(" Expr "," Expr ")"
                           | "%min"                 "(" Expr "," Expr ")"
                           | "%max"                 "(" Expr "," Expr ")"
                           | "%sha3"                "(" Expr ")"


endmodule
