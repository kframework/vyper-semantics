module VIPER-ABSTRACT-SYNTAX

    syntax Pgm ::= "%pgm" "(" Events "," Globals "," Defs ")"
                 | "%pgm" "(" Events "," Globals "," Def /*Init function*/ "," Defs ")"

    syntax Event    ::= "%event" "(" Id "," EventParams ")"
    syntax Events   ::= List{Event, ""}

    syntax EventParam  ::= "%eparam" "(" Id "," Type "," Bool /*indexed?*/ ")"
    syntax EventParams ::= List{EventParam, ""}

    syntax Global   ::= "%svdecl" "(" Id "," Type "," Visibility ")"
    syntax Globals  ::= List{Global, ""}

    syntax Visibility ::= "%public" | "%private"

    syntax Def      ::= "%fdecl" "(" Decorators "," Id "," Params "," Type "," Stmts ")"
    syntax Defs     ::= List{Def, ""}

    syntax Decorator  ::= "%@constant" | "%@payable" | "%@private" | "%@public"
    syntax Decorators ::= List{Decorator, ""}

    syntax Param    ::= "%param" "(" Id "," Type ")"
    syntax Params   ::= List{Param, ""}

    syntax Stmt     ::= VarDecl                                              // annotated assign
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
                      // stmt dispatch table
                      | "%send"      "(" Expr  "," Expr ")"
                      | "%selfdestruct" "(" Expr ")"

    syntax Stmts    ::= List{Stmt, ""}

    syntax VarDecl  ::= "%vdecl" "(" Id "," Type ")"
    syntax VarDecls ::= List{VarDecl, ""}

    syntax AugAssignOp ::= "+=" | "-=" | "*=" | "/=" | "%="

    syntax Expr     ::= Const
                      | Var
                      | ListExpr
                      | "%self"
                      | "%binop"     "(" BinOp     "," Expr "," Expr ")"
                      | "%compareop" "(" CompareOp "," Expr "," Expr ")"
                      | "%boolop"    "(" BoolOp    "," Expr "," Expr ")"
                      | "%unaryop"   "(" UnaryOp   "," Expr ")"
                      | "%icall"     "(" Id        "," Exprs ")"  // internal contract call
                      | "%ecall"     "(" Id        "," Exprs ")"  // external contract call
                      | ReservedExpr
                      | ReservedFunc  // expr dispatch table

    syntax Exprs    ::= List{Expr, ""}    [klabel("ExprList")]

    syntax Const    ::= Int
                      | "%hex"     "(" String ")"
                      | "%fixed10" "(" Int "," Int ")"  // decimal fixed point value with a precision of 10 decimal places
                                                        // %fixed10(A, B) = A/B and B is a power of 10.
                      | String
                      | Bool

    syntax Var      ::= "%var"  "(" Id ")"
                      | "%svar" "(" Id ")"
                      | StructFieldVar
                      | SubscriptVar

    syntax StructFieldVar  ::= "%attribute" "(" Var "," Id   ")"  // struct field access

    syntax SubscriptVar    ::= "%subscript" "(" Var "," Expr ")"  // list or map element

    syntax ListExpr      ::= "%list" "(" Exprs ")"

    syntax ReservedExpr  ::= "%balance" "(" Expr ")" | "%codesize" "(" Expr ")" | "%is_contract" "(" Expr ")"
                           | "%msg.sender" | "%msg.value" | "%msg.gas"
                           | "%block.difficulty" | "%block.timestamp" | "%block.coinbase" | "%block.number" | "%block.prevhash"
                           | "%tx.origin"

    syntax ReservedFunc  ::= "%as_num128"    "(" Expr ")"
                           | "%as_num256"    "(" Expr ")"
                           | "%as_wei_value" "(" Expr "," Id   ")"
                           | "%num256_add"   "(" Expr "," Expr ")"
                           | "%num256_sub"   "(" Expr "," Expr ")"

    syntax Unit          ::= BaseUnit
                           | "%umul" "(" Unit "," Unit ")"
                           | "%udiv" "(" Unit "," Unit ")"
                           | "%upow" "(" BaseUnit "," Int ")"

    syntax BaseUnit      ::= "%wei" | "%currency" | "%currency1" | "%currency2"
                           | "%sec" | "%m"        | "%kg"

    syntax Type          ::= "%void"
                           | BaseType
                           | ByteArrayType
                           | ListType
                           | MappingType
                           | StructType

    syntax BaseType      ::= "%bool"
                           | NumericType | "%num256"  | "%signed256"
                           | "%bytes32"  | "%address"

    syntax NumericType   ::= PureNumType
                           | UnitType

    syntax PureNumType   ::= "%num" | "%decimal"

    syntax UnitType      ::= "%unitT" "(" PureNumType "," Unit "," Bool /*positional*/ ")"
                           | "%timestamp"      | "%timedelta"
                           | "%currency_value" | "%currency1_value" | "%currency2_value" | "%wei_value"

    syntax ByteArrayType ::= "%bytesT"  "(" Int ")"

    syntax ListType      ::= "%listT"   "(" Type "," Int ")"

    syntax MappingType   ::= "%mapT"    "(" Type "," Type ")"

    syntax StructType    ::= "%structT" "(" VarDecls ")"

    syntax BinOp         ::= "+" | "-" | "*" | "/" | "%" | "**"

    syntax CompareOp     ::= "%lt" | "%le" | "%gt" | "%ge" | "%eq" | "%ne" | "%in"

    syntax BoolOp        ::= "%and" | "%or"

    syntax UnaryOp       ::= "%not" | "%neg"

    syntax Id            ::= ReservedWord

    syntax ReservedWord  ::= "__init__" [token]
                           | "wei"  [token]
                           | "kwei" [token] | "ada" [token] | "lovelace" [token]
                           | "babbage" [token]
                           | "shannon" [token] | "gwei" [token]
                           | "szabo"   [token]
                           | "finney"  [token]
                           | "ether"   [token]

endmodule
