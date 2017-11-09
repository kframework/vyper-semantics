module UTILS
  imports STRING

//////////////////////////////////////////////////////////////////////////////
// Constants
//////////////////////////////////////////////////////////////////////////////


    syntax Int  ::= "#reservedMemPos"     [function]
    syntax Int  ::= "#addrSizePos"        [function]
    syntax Int  ::= "#maxNumPos"          [function]
    syntax Int  ::= "#minNumPos"          [function]
    syntax Int  ::= "#maxDecimalPos"      [function]
    syntax Int  ::= "#minDecimalPos"      [function]
    syntax Int  ::= "#freeVarPos"         [function]
    syntax Int  ::= "#blankPos"           [function]
    syntax Int  ::= "#freeLoopIndexPos"   [function]
    syntax Int  ::= "#decimalDivisor"     [function]
 // ------------------------------------------------
    rule #reservedMemPos => 320
    rule #addrSizePos => 32
    rule #maxNumPos => 64
    rule #minNumPos => 96
    rule #maxDecimalPos => 128
    rule #minDecimalPos => 160
    rule #freeVarPos => 192
    rule #blankPos => 224
    rule #freeLoopIndexPos => 256
    rule #decimalDivisor => 10000000000


//////////////////////////////////////////////////////////////////////////////
// Functions
//////////////////////////////////////////////////////////////////////////////


    syntax Int       ::= "#ceil32" "(" Int ")"     [function]
 // ---------------------------------------------------------
    rule #ceil32(I) => I +Int 31 -Int (I -Int 1) %Int 32

endmodule
