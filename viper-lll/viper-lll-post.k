require "../common/lll-abstract-syntax.k"
require "viper-lll.k"

module VIPER-LLL-POST
    imports VIPER-LLL

 // -----------------------------------------------------------------
    rule $%seq(EXPRS) => #convertSeqExp(EXPRS)             [anywhere]
    rule $%seq(EXPR, .LLLExps) => EXPR
    rule $%seq(EXPR, (EXPR1, EXPRS)) => $seq(EXPR, $%seq(EXPR1, EXPRS))

endmodule 
