require "evm-core-syntax.k"

module XEVM-SYNTAX
    imports EVM-CORE-SYNTAX

    syntax XEVM ::= EVMCORE
                //| "LOG"       "(" Int ")"
                  | "DUP"       "(" Int ")"
                  | "SWAP"      "(" Int ")"
                  | "PUSH"      "(" Int "," Bytes ")"
                  | "PUSH"      "(" Label ")"
                  | "JUMP"      "(" Label ")"
                  | "JUMPI"     "(" Label ")"
                  | "JUMPDEST"  "(" Label ")"
                  | "CODELEN"

    syntax Label ::= "label" "(" Int ")"
                   | "pc"

    syntax Bytes ::= List{Int,""}

endmodule
