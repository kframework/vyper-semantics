require "../common/lll-abstract-syntax.k"
require "viper-lll.k"

module VIPER-LLL-POST
    imports VIPER-LLL

    syntax LLLExp   ::= "#convertSeqExp" "(" LLLExps ")"   [function]
 // -----------------------------------------------------------------
    rule $%seq(EXPRS) => #convertSeqExp(EXPRS)             [anywhere]
    rule #convertSeqExp(EXPR, .LLLExps) => EXPR
    rule #convertSeqExp(EXPR, (EXPR1, EXPRS)) => $seq(EXPR, #convertSeqExp(EXPR1, EXPRS))

endmodule 
