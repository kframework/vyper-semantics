module XEVM-SYNTAX

    syntax XEVM ::= "MSTORE"
                  | "MLOAD"
                  | PUSH(Int, Bytes) | PUSH(Label)
                  | DUP(Int)
                  | SWAP(Int)
                  | "POP"
                  | "ISZERO"
                  | JUMP(Label)
                  | JUMPI(Label)
                  | JUMPDEST(Label)
                  | "PC"
                  | "RETURN"
                  | "CODECOPY"
                  | "SUB"
                  | "EQ"
                  | "CALLDATALOAD"
                  | "CALLVALUE"
                  | "STOP"

    syntax Label ::= label(Int)
                   | "pc"

    syntax Bytes ::= List{Int,""}

endmodule
