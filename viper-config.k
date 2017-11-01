require "viper-lll-interface.k"
require "utils.k"

module VIPER-CONFIG
    imports VIPER-LLL-INTERFACE
    imports VIPER-SYNTAX
    imports LLL-SYNTAX
    imports UTILS

    configuration
    <T>
        <k> #compileViperToLLL($PGM:Pgm) </k>
        <lll> .K </lll>
        <env> .Map </env>
        <global> .Map </global>
        <nextStorage> 0 </nextStorage>
        <nextMem> #reservedMemPos </nextMem>
        <forvar> .Set </forvar>
        <return> %void </return>
        <constant> false </constant>
        <payable> false </payable>
    </T>

endmodule
