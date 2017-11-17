require "../common/lll-abstract-syntax.k"
require "xevm-syntax.k"

module LLL-XEVM-INTERFACE
    imports LLL-ABSTRACT-SYNTAX
    imports XEVM-SYNTAX

    syntax Label ::= "emptyLabel" [function]
    syntax Int ::= "emptyHeight" [function]
endmodule
