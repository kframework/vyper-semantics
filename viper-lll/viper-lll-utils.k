module VIPER-LLL-UTILS
  imports STRING

//////////////////////////////////////////////////////////////////////////////
// Constants
//////////////////////////////////////////////////////////////////////////////


    syntax Int  ::= "@reservedMemPos"
    syntax Int  ::= "@addrSizePos"
    syntax Int  ::= "@maxNumPos"
    syntax Int  ::= "@minNumPos"
    syntax Int  ::= "@maxDecimalPos"
    syntax Int  ::= "@minDecimalPos"
    syntax Int  ::= "@freeVarPos"
    syntax Int  ::= "@blankPos"
    syntax Int  ::= "@freeLoopIndexPos"
    syntax Int  ::= "@decimalDivisor"
 // -----------------------------------
    rule @reservedMemPos => 320          [macro]
    rule @addrSizePos => 32              [macro]
    rule @maxNumPos => 64                [macro]
    rule @minNumPos => 96                [macro]
    rule @maxDecimalPos => 128           [macro]
    rule @minDecimalPos => 160           [macro]
    rule @freeVarPos => 192              [macro]
    rule @blankPos => 224                [macro]
    rule @freeLoopIndexPos => 256        [macro]
    rule @decimalDivisor => 10000000000  [macro]


//////////////////////////////////////////////////////////////////////////////
// Functions
//////////////////////////////////////////////////////////////////////////////


    syntax Int       ::= "#ceil32" "(" Int ")"     [function]
 // ---------------------------------------------------------
    rule #ceil32(I) => I +Int 31 -Int (I -Int 1) %Int 32

endmodule
