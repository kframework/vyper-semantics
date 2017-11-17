require "lll-syntax.k"
require "xevm-syntax.k"

module LLL-XEVM-INTERFACE
    imports LLL-SYNTAX
    imports XEVM-SYNTAX

    syntax Label ::= "emptyLabel" [function]
    syntax Int ::= "emptyHeight" [function]
endmodule
