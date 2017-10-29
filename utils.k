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


//////////////////////////////////////////////////////////////////////////////
// Utils
//////////////////////////////////////////////////////////////////////////////


    syntax Int  ::= "#hex2Int"       "(" String ")"          [function]
    syntax Int  ::= "#hex2IntHelper" "(" String "," Int ")"  [function]
    syntax Int  ::= "#hexChar2Int"   "(" String ")"          [function]
 // -------------------------------------------------------------------
    rule #hex2Int(STR) => #hex2IntHelper(STR, 0)

    rule #hex2IntHelper(STR, N) => N
      requires lengthString(STR) ==Int 0

    rule #hex2IntHelper(STR, N) => (N *Int 16) +Int #hexChar2Int(STR)
      requires lengthString(STR) ==Int 1

    rule #hex2IntHelper(STR, N)
             => #hex2IntHelper(substrString(STR, 1, lengthString(STR)),
                               (N *Int 16) +Int #hexChar2Int(substrString(STR, 0, 1)))
      requires lengthString(STR) >Int 1

    rule #hexChar2Int("0") => 0
    rule #hexChar2Int("1") => 1
    rule #hexChar2Int("2") => 2
    rule #hexChar2Int("3") => 3
    rule #hexChar2Int("4") => 4
    rule #hexChar2Int("5") => 5
    rule #hexChar2Int("6") => 6
    rule #hexChar2Int("7") => 7
    rule #hexChar2Int("8") => 8
    rule #hexChar2Int("9") => 9
    rule #hexChar2Int("a") => 10
    rule #hexChar2Int("b") => 11
    rule #hexChar2Int("c") => 12
    rule #hexChar2Int("d") => 13
    rule #hexChar2Int("e") => 14
    rule #hexChar2Int("f") => 15

endmodule
