requires "../types.k"

module TEST-HARNESS-SYNTAX
  imports MINISIG-TYPES

  syntax LstBool ::= List{Bool, ":"}

  syntax StateIdInt ::= "nonce"
                      | "balance"
                      | "threshold"

  syntax StateExp ::= StateIdInt ":=" Int
                    | "domSep" ":=" String
                    | "signers" ":=" "[" LstAddress "]"
                    | StateExp StateExp [left]

  syntax WorldExp ::= "gas-used-pre-call"           ":=" Int
                    | "codesize" "[" Address "]"    ":=" Int
                    | "ecrecover" "[" SignedMsg "]" ":=" Address
                    | "call-success"                ":=" "[" LstBool "]"
                    | WorldExp WorldExp [left]

  syntax Setup ::= "setState" StateExp
                 | "setWorld" WorldExp
                 | Setup Setup [left]

  syntax Test ::= Setup
                | Setup Tx

endmodule
