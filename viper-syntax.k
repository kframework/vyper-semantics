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
    syntax Stmts    ::= List{Stmt, ""}

    syntax VarDecl  ::= "%vdecl" "(" Id "," Type ")"
    syntax VarDecls ::= List{VarDecl, ""}

    syntax AugAssignOp ::= "+=" | "-=" | "*=" | "/=" | "%="

    syntax Var      ::= "%var"  "(" Id ")"
                      | "%svar" "(" Id ")"
                      | "%mem"  "(" Var "," Id ")"
                      | "%arr"  "(" Var "," Expr ")"

    syntax Expr     ::= Const | Var
                      | "%const"    "(" Const ")"
                      | "%binop"    "(" BinOp    "," Expr "," Expr ")"
                      | "%unaryop"  "(" UnaryOp  "," Expr ")"
                      | "%typecast" "(" BaseType "," Expr ")"
                      | "%floor"    "(" Expr ")"

    syntax Const    ::= Int | String

    syntax Type          ::= BaseType
                           | "%void"
                           | "%map"    "(" Type "," BaseType ")"
                           | "%array"   "(" Type "," Int ")"
                           | ByteArrayType
                           | StructType
    syntax StructType    ::= "%struct" "(" VarDecls ")"

    syntax ByteArrayType ::= "%bytes"  "(" Int ")"

    syntax BaseType      ::= "%num" | "%decimal" | "%bool" | "%address" | "%bytes32"

    syntax BinOp         ::= "+" | "-" | "*" | "/" | "%"
                           | "and" | "or"
                           | "<" | "<=" | ">" | ">=" | "==" | "!="

    syntax UnaryOp       ::= "not"

    syntax Id            ::= "__init__"

endmodule
