require "../common/lll-abstract-syntax.k"
require "viper-lll.k"

module VIPER-LLL-POST
    imports VIPER-LLL

 // -----------------------------------------------------------------
    rule $%seq(EXPR, .LLLExps) => EXPR
    rule $%seq(EXPR1, (EXPR2, EXPRS)) => $seq(EXPR1, $%seq(EXPR2, EXPRS))

endmodule 
