module VIPER-SYNTAX

    syntax Pgm ::= "%pgm" "(" Globals "," Defs ")"
                 | "%pgm" "(" Globals "," Def /*Init function*/ "," Defs ")"

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
                      | "%return"    "(" Expr ")"
                      | "%send"      "(" Expr "," Expr ")"
                      | "%selfdestruct" "(" Expr ")"
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

    syntax Var      ::= "%var"      "(" Id ")"
                      | "%svar"     "(" Id ")"
                      | "%mem"      "(" Var "," Id ")"     /*field access*/
                      | "%listelem" "(" Var "," Expr ")"   /*list element*/
                      | "%mapelem"  "(" Var "," Expr ")"   /*map element*/

    syntax Const    ::= Int
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

    syntax NumericType   ::= "%num" | "%decimal"
                           | UnitType

    syntax UnitType      ::= "%unit" "(" NumericType "," Unit "," Bool /*positional*/ ")"

    syntax ByteArrayType ::= "%bytes"  "(" Int ")"

    syntax ListType      ::= "%list"   "(" Type "," Int ")"

    syntax MappingType   ::= "%map"    "(" Type "," BaseType ")"

    syntax StructType    ::= "%struct" "(" VarDecls ")"

    syntax BinOp         ::= "+" | "-" | "*" | "/" | "%"

    syntax CompareOp     ::= "%lt" | "%le" | "%gt" | "%ge" | "%eq" | "%ne"

    syntax BoolOp        ::= "%and" | "%or"

    syntax UnaryOp       ::= "%not" | "%neg"

    syntax Id            ::= "__init__"
                           | "wei"    | "kwei" | "ada"   | "lovelace" | "babbage"
                           | "shannon"| "gwei" | "szabo" | "finney"   | "ether"

endmodule
