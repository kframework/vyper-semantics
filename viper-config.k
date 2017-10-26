require "viper-lll-interface.k"
require "lll-evm-interface.k"
require "utils.k"

module VIPER-CONFIG
    imports VIPER-LLL-INTERFACE
    imports LLL-EVM-INTERFACE
    imports VIPER-SYNTAX
    imports LLL-SYNTAX
    imports UTILS

    configuration
    <T>
        <k> #compileViperToLLL($PGM:Pgm) </k>
        <lll> .LLLExps </lll>
        <lllCodeStack> .List </lllCodeStack>
        <env> .Map </env>
        <global> .Map </global>
        <nextStorage> 0 </nextStorage>
        <nextMem> #reservedMemPos </nextMem>
    </T>

endmodule
