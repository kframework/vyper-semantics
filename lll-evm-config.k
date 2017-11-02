require "lll-xevm-interface.k"
require "xevm-evm-interface.k"

module LLL-EVM-CONFIG

    imports LLL-XEVM-INTERFACE
    imports XEVM-EVM-INTERFACE

    configuration <T>
      <k> $PGM:LLLExp ~> xevm2evm </k>
      <xevm> .List </xevm> // XEVM*
      <evm> .List </evm> // EVM*
      <height> 0 </height>
      <with> .Map </with> // Var -> StackLoc
      <b> // NOTE: mean break, but parser confuses with <br>
        <b-label> emptyLabel </b-label>
        <b-height> emptyHeight </b-height>
      </b>
      <labelTbl> .Map </labelTbl>
      <pos> 0 </pos>
      <posStack> .List </posStack>
    </T>

endmodule
