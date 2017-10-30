module XEVM-SYNTAX

    syntax XEVM ::= YEVM
                  | "DUP"       "(" Int ")"
                  | "SWAP"      "(" Int ")"
                  | "PUSH"      "(" Int "," Bytes ")"
                  | "PUSH"      "(" Label ")"
                  | "JUMP"      "(" Label ")"
                  | "JUMPI"     "(" Label ")"
                  | "JUMPDEST"  "(" Label ")"

    syntax YEVM ::= "STOP"
                  | "ADD"
                  | "MUL"
                  | "SUB"
                  | "DIV"
                  // ...
                  | "LT"
                  | "GT"
                  | "SLT"
                  | "SGT"
                  | "EQ"
                  | "ISZERO"
                  // ...
                  | "SHA3"
                  // ...
                  | "CALLVALUE"
                  | "CALLDATALOAD"
                  | "CODECOPY"
                  // ...
                  | "POP"
                  | "MLOAD"
                  | "MSTORE"
                  | "PC"
                  | "RETURN"

    syntax Label ::= "label" "(" Int ")"
                   | "pc"

    syntax Bytes ::= List{Int,""}

endmodule
