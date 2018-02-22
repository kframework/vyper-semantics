





module KRYPTO
    imports DOMAINS









    syntax String ::= Keccak256 ( String )                            [function, hook(KRYPTO.keccak256)]
                    | ECDSARecover ( String , Int , String , String ) [function, hook(KRYPTO.ecdsaRecover)]
                    | Sha256 ( String )                               [function, hook(KRYPTO.sha256)]
                    | RipEmd160 ( String )                            [function, hook(KRYPTO.ripemd160)]
 // ----------------------------------------------------------------------------------------------------










    syntax G1Point ::= "(" Int "," Int ")"
    syntax G2Point ::= "(" Int "x" Int "," Int "x" Int ")"
    syntax G1Point ::= BN128Add(G1Point, G1Point) [function, hook(KRYPTO.bn128add)]
                     | BN128Mul(G1Point, Int)     [function, hook(KRYPTO.bn128mul)]
 // -------------------------------------------------------------------------------

    syntax Bool ::= BN128AtePairing(List, List) [function, hook(KRYPTO.bn128ate)]
 // -----------------------------------------------------------------------------

    syntax Bool ::= isValidPoint(G1Point) [function, hook(KRYPTO.bn128valid)]
                  | isValidPoint(G2Point) [function, klabel(isValidG2Point), hook(KRYPTO.bn128g2valid)]
 // ---------------------------------------------------------------------------------------------------
endmodule


