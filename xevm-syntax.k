module XEVM-SYNTAX

    syntax XEVM ::= YEVM
                  | "DUP"       "(" Int ")"
                  | "SWAP"      "(" Int ")"
                  | "PUSH"      "(" Int "," Bytes ")"
                  | "PUSH"      "(" Label ")"
                  | "JUMP"      "(" Label ")"
                  | "JUMPI"     "(" Label ")"
                  | "JUMPDEST"  "(" Label ")"

    syntax YEVM ::= "MSTORE"
                  | "MLOAD"
                  | "POP"
                  | "ISZERO"
                  | "PC"
                  | "RETURN"
                  | "CODECOPY"
                  | "SUB"
                  | "ADD"
                  | "EQ"
                  | "CALLDATALOAD"
                  | "CALLVALUE"
                  | "STOP"

    syntax Label ::= "label" "(" Int ")"
                   | "pc"

    syntax Bytes ::= List{Int,""}

endmodule
