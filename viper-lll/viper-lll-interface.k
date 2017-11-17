require "viper-syntax.k"
require "lll-syntax.k"

module VIPER-LLL-INTERFACE
    imports VIPER-SYNTAX
    imports LLL-SYNTAX

    syntax KItem ::= "#compileViperToLLL" "(" Pgm ")"

endmodule
