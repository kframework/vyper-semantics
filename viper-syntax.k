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
                      | "%for"       "(" Id "," Int "," Stmts ")"
                      | "%for"       "(" Id "," Expr "," Int "," Stmts ")"
                      | "%pass"
                      | "%return"
                      | "%break"
                      | "%return" "(" Expr ")"
                      | "%send" "(" Expr "," Expr ")"
                      | "%selfdestruct" "(" Expr ")"
                      | "%throw"
    syntax Stmts    ::= List{Stmt, ""}

    syntax VarDecl  ::= "%vdecl" "(" Id "," Type ")"
    syntax VarDecls ::= List{VarDecl, ""}

    syntax AugAssignOp ::= "+=" | "-=" | "*=" | "/=" | "%="

    syntax Var      ::= "%var"  "(" Id ")"
                      | "%svar" "(" Id ")"
                      | "%mem"  "(" Var "," Id ")"
                      | "%arr"  "(" Var "," Expr ")"
                      | "%self"

    syntax Expr     ::= Const | Var
                      | "%const"    "(" Const ")"
                      | "%binop"    "(" BinOp    "," Expr "," Expr ")"
                      | "%unaryop"  "(" UnaryOp  "," Expr ")"
                      | "%typecast" "(" BaseType "," Expr ")"
                      | "%floor"    "(" Expr ")"

    syntax Const    ::= Int | String

    syntax Type          ::= "%void"
                           | BaseType
                           | ByteArrayType
                           | ListType
                           | MappingType
                           | StructType

    syntax BaseType      ::= "%num" | "%decimal" | "%bool" | "%address" | "%bytes32"

    syntax ByteArrayType ::= "%bytes"  "(" Int ")"

    syntax ListType      ::= "%list"   "(" Type "," Int ")"

    syntax MappingType   ::= "%map"    "(" Type "," BaseType ")"

    syntax StructType    ::= "%struct" "(" VarDecls ")"

    syntax BinOp         ::= "+" | "-" | "*" | "/" | "%"
                           | "and" | "or"
                           | "<" | "<=" | ">" | ">=" | "==" | "!="

    syntax UnaryOp       ::= "not"

    syntax Id            ::= "__init__"

endmodule
