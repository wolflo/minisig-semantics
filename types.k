requires "syntax.k"

module MINISIG-TYPES
  imports MINISIG-SYNTAX

  syntax Error ::= "INVALID_VAL"
                 | "INVALID_CALLVAL"

  // --- Internal representations ---

  syntax ViewId ::= "Nonce"
                   | "Thresh"
                   | "DomSep"
                   | "Signers"
  syntax OpView ::= "View" "(" ViewId ")"

  syntax OpExec ::= "Exec" "(" "op:" CallType
                            "," "val:" Uint
                            "," "dst:" Address
                            "," "data:" Data
                            "," "sigs:" LstSig ")"
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
