module VIPER-ABSTRACT-SYNTAX

    syntax Pgm  ::= "%pgm" "(" Events "," Globals "," Defs ")"
                  | "%pgm" "(" Events "," Globals "," Def /*Init function*/ "," Defs ")"


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
                   | "%icall"     "(" Id /*func name*/ "," Arguments ")"  // internal contract call
                   | "%ecall"     "(" Argument /*address*/ "," Id /*func name*/ "," Arguments ")"  // external contract call
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

    syntax SubscriptVar  ::= "%subscript" "(" Var "," Expr ")"  // list or map element

    syntax AttributeVar  ::= "%attribute" "(" Var "," Id   ")"  // struct field access

    syntax ListExpr  ::= "%list" "(" Exprs ")"

    syntax StructExpr  ::= "%struct" "(" StructItems ")"

    syntax StructItem  ::= "%item" "(" Id "," Expr ")"
    syntax StructItems ::= List{StructItem, ""}

    syntax Argument  ::= Expr
                       | "%kwarg" "(" Id "," Expr ")"

    syntax Arguments ::= List{Argument, ""}
                       | Exprs

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
                       | "%bytes32"  | "%address"

    syntax NumericType  ::= PureNumType
                          | UnitType

    syntax PureNumType  ::= "%num" | "%decimal"

    syntax UnitType  ::= "%unitT" "(" PureNumType "," Unit "," Bool /*positional*/ ")"
                       | "%timestamp"      | "%timedelta"
                       | "%currency_value" | "%currency1_value" | "%currency2_value" | "%wei_value"

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

    syntax ReservedFunc  ::= "%floor"               "(" Argument ")"
                           | "%decimal"             "(" Argument ")"
                           | "%as_unitless_number"  "(" Argument ")"
                           | "%as_num128"           "(" Argument ")"
                           | "%as_num256"           "(" Argument ")"
                           | "%as_bytes32"          "(" Argument ")"
                           | "%slice"               "(" Argument "," Argument "," Argument ")"
                           | "%len"                 "(" Argument ")"
                           | "%concat"              "(" Arguments ")"                      //operates on byte arrays
                           | "%keccak256"           "(" Argument ")"
                           | "%method_id"           "(" Argument ")"
                           | "%ecrecover"           "(" Argument ")"
                           | "%ecadd"               "(" Argument "," Argument ")"
                           | "%ecmul"               "(" Argument "," Argument ")"
                           | "%extract32"           "(" Argument "," Argument "," Id ")"
                           | "%bytes_to_num"        "(" Argument ")"
                           | "%as_wei_value"        "(" Argument "," Id   ")"
                        // | "%raw_call"            "(" Argument "," Argument "," Argument "," Argument "," Argument ")"
                           | "%RLPlist"             "(" Argument "," Argument ")"
                           | "%blockhash"           "(" Argument ")"
                           | "%bitwise_and"         "(" Argument "," Argument ")"
                           | "%bitwise_or"          "(" Argument "," Argument ")"
                           | "%bitwise_xor"         "(" Argument "," Argument ")"
                           | "%bitwise_not"         "(" Argument ")"
                           | "%num256_add"          "(" Argument "," Argument ")"
                           | "%num256_sub"          "(" Argument "," Argument ")"
                           | "%num256_mul"          "(" Argument "," Argument ")"
                           | "%num256_div"          "(" Argument "," Argument ")"
                           | "%num256_exp"          "(" Argument "," Argument ")"
                           | "%num256_mod"          "(" Argument "," Argument ")"
                           | "%num256_addmod"       "(" Argument "," Argument "," Argument ")"
                           | "%num256_mulmod"       "(" Argument "," Argument "," Argument ")"
                           | "%num256_gt"           "(" Argument "," Argument ")"
                           | "%num256_ge"           "(" Argument "," Argument ")"
                           | "%num256_lt"           "(" Argument "," Argument ")"
                           | "%num256_le"           "(" Argument "," Argument ")"
                           | "%shift"               "(" Argument "," Argument ")"
                        // | "%create_with_code_of" "(" Argument "," Argument ")"
                           | "%min"                 "(" Argument "," Argument ")"
                           | "%max"                 "(" Argument "," Argument ")"
                           | "%sha3"                "(" Argument ")"


endmodule
