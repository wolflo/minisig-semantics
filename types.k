requires "syntax.k"

module MINISIG-TYPES
  imports DOMAINS
  imports MINISIG-SYNTAX

  // --- Internal representations ---

  syntax ViewId ::= "Nonce"
                   | "Thresh"
                   | "DomSep"
                   | "Signers"

  syntax OpView ::= "View" "(" ViewId ")"

  syntax OpExec ::= "Exec" "(" CallType
                           "," Int
                           "," Address
                           "," Data
                           "," LstSig ")"
  syntax Exp ::= OpView
               | OpExec

  rule nonce()            => View ( Nonce   ) [macro]
  rule threshold()        => View ( Thresh  ) [macro]
  rule allSigners()       => View ( Signers ) [macro]
  rule DOMAIN_SEPARATOR() => View ( DomSep  ) [macro]

  rule execute( OP, VAL, DST, DATA, [ SIGS ] )
    => Exec ( OP , VAL , DST , DATA , SIGS )  [macro]

  // --- Signatures ---

  syntax SignedMsg ::= "{" "sig:" Sig
                       "," "nonce:" Int
                       "," "op:" CallType
                       "," "val:" Int
                       "," "dst:" Address
                       "," "data:" Data "}"

  syntax LstAddress ::= List{Address, ":"}
  syntax LstSignedMsg ::= List{SignedMsg, ":"}

  syntax SignedMsg ::= "#toSignedMsg" CallType Int Address Data Int Sig [function]

  rule #toSignedMsg OP VAL DST DATA NONCE SIG
    => { sig: SIG, nonce: NONCE, op: OP, val: VAL, dst: DST, data: DATA }

  syntax LstSignedMsg ::= "#toLstSignedMsg" CallType Int Address Data Int LstSig [function]

  rule #toLstSignedMsg _ _ _ _ _ .LstSig => .LstSignedMsg

  rule #toLstSignedMsg OP VAL DST DATA NONCE ( SIG , SIGS )
    => #toSignedMsg OP VAL DST DATA NONCE SIG
       : #toLstSignedMsg OP VAL DST DATA NONCE SIGS

  // --- Errors and Logs ---

  syntax Error ::= "INVALID_VAL"
                 | "INVALID_CALLVAL"
                 | "DELEGATECALL_DST_EMPTY_CODE"
                 | "ZERO_ADDRESS_SIGNER"
                 | "EMPTY_SIGNERS"
                 | "SIGS_UNORDERED"
                 | "INSUFFICIENT_VALID_SIGS"
                 | "INVALID_POSTSTATE"
                 | "UNSPECIFIED"

  syntax FnDetails ::= "fn_nonce()"
                     | "fn_threshold()"
                     | "fn_DOMAIN_SEPARATOR()"
                     | "fn_allSigners()"
                     | "fn_execute" "(" CallType
                                    "," Int
                                    "," Address
                                    "," Data
                                    "," "[" LstSig "]" ")"

  syntax FnLog ::= "{" "fn:"         FnDetails
                   "," "callvalue:"  Int
                   "," "returndata:" RetVal "}"

  syntax CallLog ::= "{" "op:"   CallType
                     "," "val:"  Int
                     "," "dst:"  Address
                     "," "data:" Data "}"

  syntax RetVal ::= ".RetVal"
                  | Bool
                  | Int
                  | Set

  // --- Utils ---

  syntax LstSignedMsg ::= "#take" Int LstSignedMsg [function]
  rule #take _ .LstSignedMsg => .LstSignedMsg
  rule #take 0 _             => .LstSignedMsg
  rule #take N ( X : XS )    => X : ( #take (N -Int 1) XS )
    requires N >Int 0

  syntax Set ::= "#toSet" LstAddress [function]
  rule #toSet .LstAddress => .Set
  rule #toSet X : XS => SetItem(X) ( #toSet XS )

  syntax Int ::= "pow256" // 2 ^ 256
  rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936 [macro]

endmodule
