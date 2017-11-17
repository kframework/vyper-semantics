module VIPER-SYNTAX

    syntax Pgm ::= "%pgm" "(" Events "," Globals "," Defs ")"
                 | "%pgm" "(" Events "," Globals "," Def /*Init function*/ "," Defs ")"

    syntax Event    ::= "%event" "(" Id "," EventParams ")"
    syntax Events   ::= List{Event, ""}

    syntax EventParam  ::= "%eparam" "(" Id "," Type "," Bool ")"
    syntax EventParams ::= List{EventParam, ""}

    syntax Global   ::= "%svdecl" "(" Id "," Type "," Visibility ")"
    syntax Globals  ::= List{Global, ""}

    syntax Visibility ::= "%public" | "%private"

    syntax Def      ::= "%fdecl" "(" Decorators "," Id "," Params "," Type "," Stmts ")"
    syntax Defs     ::= List{Def, ""}

    syntax Decorator  ::= "%@constant" | "%@payable" | "%@internal"
    syntax Decorators ::= List{Decorator, ""}

    syntax Param    ::= "%param" "(" Id "," Type ")"
    syntax Params   ::= List{Param, ""}

    syntax Stmt     ::= VarDecl
                      | "%assign"    "(" Var "," Expr ")"
                      | "%augassign" "(" AugAssignOp "," Var "," Expr ")"
                      | "%if"        "(" Expr "," Stmts "," Stmts ")"
                      | "%if"        "(" Expr "," Stmts ")"
                      | "%for"       "(" Id "," Int "," Stmts ")"
                      | "%for"       "(" Id "," Expr "," Expr "," Stmts ")"
                      | "%break"
                      | "%pass"
                      | "%return"
                      | "%return"    "(" Expr  ")"
                      | "%send"      "(" Expr  "," Expr ")"
                      | "%selfdestruct" "(" Expr ")"
                      | "%log"       "(" Id "," Exprs ")"
                      | "%throw"
    syntax Stmts    ::= List{Stmt, ""}

    syntax VarDecl  ::= "%vdecl" "(" Id "," Type ")"
    syntax VarDecls ::= List{VarDecl, ""}

    syntax AugAssignOp ::= "+=" | "-=" | "*=" | "/=" | "%="

    syntax Expr     ::= Const
                      | Var
                      | ReservedExpr
                      | ReservedFunc
                      | "%self"
                      | "%binop"     "(" BinOp     "," Expr "," Expr ")"
                      | "%compareop" "(" CompareOp "," Expr "," Expr ")"
                      | "%boolop"    "(" BoolOp    "," Expr "," Expr ")"
                      | "%unaryop"   "(" UnaryOp   "," Expr ")"
                      | "%typecast"  "(" BaseType  "," Expr ")"
                      | "%floor"     "(" Expr ")"
    syntax Exprs    ::= List{Expr, ","}

    syntax Var      ::= "%var"      "(" Id ")"
                      | "%svar"     "(" Id ")"
                      | "%mem"      "(" Var "," Id ")"     /*field access*/
                      | "%listelem" "(" Var "," Expr ")"   /*list element*/
                      | "%mapelem"  "(" Var "," Expr ")"   /*map element*/

    syntax Const    ::= Int
                      | "%hex" "(" String ")"
                      | String
                      | Bool

    syntax ReservedExpr  ::= "%msg.sender" | "%msg.value" | "%msg.gas"
                           | "%block.difficulty" | "%block.timestamp" | "%block.coinbase" | "%block.number" | "%block.prevhash"
                           | "%tx.origin"

    syntax ReservedFunc  ::= "%as_num128"    "(" Expr ")"
                           | "%as_num256"    "(" Expr ")"
                           | "%as_wei_value" "(" Expr "," Id   ")"
                           | "%num256_add"   "(" Expr "," Expr ")"
                           | "%num256_sub"   "(" Expr "," Expr ")"


    syntax Unit          ::=  BaseUnit
                           |  Unit "*" Unit       [left]
                           |  Unit "/" Unit       [left]


    syntax BaseUnit      ::= "%wei" | "%currency" | "%currency1" | "%currency2"
                           | "%sec" | "%m"        | "%kg"


    syntax Type          ::= "%void"
                           | BaseType
                           | ByteArrayType
                           | ListType
                           | MappingType
                           | StructType

    syntax BaseType      ::= NumericType
                           | "%bytes32" | "%num256" | "%bool" | "%address"

    syntax NumericType   ::= PureNumType
                           | UnitType

    syntax PureNumType   ::= "%num" | "%decimal"

    syntax UnitType      ::= "%unitT" "(" PureNumType "," Unit "," Bool /*positional*/ ")"

    syntax ByteArrayType ::= "%bytesT"  "(" Int ")"

    syntax ListType      ::= "%listT"   "(" Type "," Int ")"

    syntax MappingType   ::= "%mapT"    "(" Type "," BaseType ")"

    syntax StructType    ::= "%structT" "(" VarDecls ")"

    syntax BinOp         ::= "+" | "-" | "*" | "/" | "%" | "**"

    syntax CompareOp     ::= "%lt" | "%le" | "%gt" | "%ge" | "%eq" | "%ne"

    syntax BoolOp        ::= "%and" | "%or"

    syntax UnaryOp       ::= "%not" | "%neg"

    syntax Id            ::= ReservedWord

    syntax ReservedWord  ::= "__init__" [token]
                           | "wei" [token]
                           | "kwei" [token] | "ada" [token] | "lovelace" [token]
                           | "babbage" [token]
                           | "shannon" [token] | "gwei" [token]
                           | "szabo" [token]
                           | "finney" [token]
                           | "ether" [token]

endmodule
