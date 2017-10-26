module LLL-SYNTAX

    syntax LLLExp ::= LLLConst
                    | LLLEVM
                    | "$set"           "(" LLLExp "," LLLExp ")"
                    | "$pass"
                    | "$codeload"      "(" LLLExp ")"
                    | "$if"            "(" LLLExp "," LLLExp ")"
                    | "$if"            "(" LLLExp "," LLLExp "," LLLExp ")"
                    | "$repeat"        "(" LLLExp "," LLLExp "," LLLExp "," LLLExp ")"
                    | "$break"
                    | "$with"          "(" LLLExp "," LLLExp "," LLLExp ")"
                    | "$lll"           "(" LLLExp "," LLLExp ")"
                    | "$seq"           "(" LLLExps ")"
                    | "$assert"        "(" LLLExp ")"
                    | "$uclamplt"      "(" LLLExp "," LLLExp ")"
                    | "$uclample"      "(" LLLExp "," LLLExp ")"
                    | "$clamplt"       "(" LLLExp "," LLLExp ")"
                    | "$clample"       "(" LLLExp "," LLLExp ")"
                    | "$uclampgt"      "(" LLLExp "," LLLExp ")"
                    | "$uclampge"      "(" LLLExp "," LLLExp ")"
                    | "$clampgt"       "(" LLLExp "," LLLExp ")"
                    | "$clampge"       "(" LLLExp "," LLLExp ")"
                    | "$clamp"         "(" LLLExp "," LLLExp "," LLLExp ")"
                    | "$uclamp"        "(" LLLExp "," LLLExp "," LLLExp ")"
                    | "$clamp_nonzero" "(" LLLExp ")"
                    | "$sha3_32"       "(" LLLExp ")"
                    | "$le"            "(" LLLExp "," LLLExp ")"
                    | "$ge"            "(" LLLExp "," LLLExp ")"
                    | "$sle"           "(" LLLExp "," LLLExp ")"
                    | "$sge"           "(" LLLExp "," LLLExp ")"
                    | "$ne"            "(" LLLExp "," LLLExp ")"
                    | "$ceil32"        "(" LLLExp ")"

    syntax LLLEVM ::= "$mstore"        "(" LLLExp "," LLLExp ")"
                    | "$mload"         "(" LLLExp ")"
                    | "$sstore"        "(" LLLExp "," LLLExp ")"
                    | "$sload"         "(" LLLExp ")"
                    | "$codecopy"      "(" LLLExp "," LLLExp "," LLLExp ")"
                    | "$calldataload"  "(" LLLExp ")"
                    | "$calldatacopy"  "(" LLLExp "," LLLExp "," LLLExp ")"
                    | "$eq"            "(" LLLExp "," LLLExp ")"
                    | "$iszero"        "(" LLLExp ")"

    syntax LLLExps ::= List{LLLExp, ";"}

    syntax LLLConst ::= Int | "~codelen" | "callvalue" | "caller" | "address"

    syntax LLLExps ::= "#extLLL" "(" LLLExps "," LLLExps ")"    [function]
 // -------------------------------------------------------------------------
    rule #extLLL(.LLLExps, LES) => LES
    rule #extLLL(E ; ES1, ES2) => E ; #extLLL(ES1, ES2)

endmodule
