requires "syntax.k"

module MINISIG-TYPES
  imports DOMAINS
  imports MINISIG-SYNTAX

  // --- Errors and Logs ---

  syntax Error ::= "INVALID_VAL"
                 | "INVALID_CALLVAL"
                 | "UNSPECIFIED"

  syntax FnDetails ::= "execute"
                     | "nonce"
                     | "threshold"
                     | "DOMAIN_SEPARATOR"
                     | "allSigners"

  syntax FnLog ::= "{" "fn:" FnDetails "," "callvalue:" Int "," "return:" KItem "}"

  // --- Internal representations ---

  syntax ViewId ::= "Nonce"
                   | "Thresh"
                   | "DomSep"
                   | "Signers"

  syntax OpView ::= "View" "(" ViewId ")"

  syntax OpExec ::= "Exec" "(" CallType
                           "," Uint
                           "," Address
                           "," Data
                           "," LstSig ")"
  syntax Exp ::= OpView
               | OpExec

  rule nonce()            => View ( Nonce   ) [macro]
  rule threshold()        => View ( Thresh  ) [macro]
  rule allSigners()       => View ( Signers ) [macro]
  rule DOMAIN_SEPARATOR() => View ( DomSep  ) [macro]

  rule execute( OP, VAL, DST, DATA, [SIGS] ) => Exec ( op: OP
                                                     , val: VAL
                                                     , dst: DST
                                                     , data: DATA
                                                     , sigs: SIGS) [macro]

endmodule
