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
                           "," Int
                           "," Address
                           "," Data
                           "," LstSig ")"

  syntax OpCstr ::= "Cstr" "(" Int "," LstAddress ")"

  syntax OpLog ::= "#log" FnDetails
  syntax OpSet ::= "#set" LstOpt

  syntax Exp ::= OpView
               | OpExec
               | OpLog
               | OpCstr

  // if options are provided, set the options then execute the function
  rule FN { OPTS } PARAMS => #set OPTS ~> FN PARAMS   [simplification]

  rule nonce()            => #log fn_nonce()
                          ~> View ( Nonce )             [simplification]
  rule threshold()        => #log fn_threshold()
                          ~> View ( Thresh )            [simplification]
  rule allSigners()       => #log fn_allSigners()
                          ~> View ( Signers )           [simplification]
  rule DOMAIN_SEPARATOR() => #log fn_DOMAIN_SEPARATOR()
                          ~> View ( DomSep)             [simplification]

  rule execute ( OP, GAS, VAL, DST, DATA, [ SIGS ] )
    => #log fn_execute ( OP , GAS , VAL , DST , DATA , [ SIGS ] )
    ~> Exec ( OP , GAS , VAL , DST , DATA , SIGS )    [simplification]

  rule constructor ( THRESHOLD , [ SIGNERS ] )
    => #log fn_constructor ( THRESHOLD , SIGNERS)
    ~> Cstr ( THRESHOLD , SIGNERS )

  // --- Signatures ---

  syntax SignedMsg ::= "{" "sig:"   Sig
                       "," "op:"    CallType
                       "," "nonce:" Int
                       "," "gas:" Int
                       "," "val:"   Int
                       "," "dst:"   Address
                       "," "data:"  Data "}"

  syntax LstSignedMsg ::= List{SignedMsg, ":"}

  syntax SignedMsg ::= "#toSignedMsg" CallType Int Int Address Data Int Sig [function]

  rule #toSignedMsg OP GAS VAL DST DATA NONCE SIG
    => { sig: SIG, op: OP, nonce: NONCE, gas: GAS, val: VAL, dst: DST, data: DATA }

  syntax LstSignedMsg ::= "#toLstSignedMsg" CallType Int Int Address Data Int LstSig [function]

  rule #toLstSignedMsg _ _ _ _ _ _ .LstSig => .LstSignedMsg

  rule #toLstSignedMsg OP GAS VAL DST DATA NONCE ( SIG : SIGS )
    => #toSignedMsg OP GAS VAL DST DATA NONCE SIG
       : #toLstSignedMsg OP GAS VAL DST DATA NONCE SIGS

  // --- Errors and Logs ---

  syntax MsigStatus ::= ".Status"
                      | "MSIG_SUCCESS"
                      | "MSIG_REVERT"

  syntax Error ::= "INVALID_VAL"
                 | "INVALID_CALLVAL"
                 | "DELEGATECALL_INVALID_CALLVAL"
                 | "DELEGATECALL_DST_EMPTY_CODE"
                 | "ZERO_ADDRESS_SIGNER"
                 | "EMPTY_SIGNERS"
                 | "SIGNERS_UNORDERED"
                 | "INSUFFICIENT_VALID_SIGS"
                 | "INVALID_POSTSTATE"
                 | "CALL_FAILED"
                 | "INVALID_THRESHOLD"
                 | "INSUFFICIENT_SIGNERS"
                 | "INSUFFICIENT_CALLGAS"
                 | "UNSPECIFIED"

  syntax FnDetails ::= "fn_nonce()"
                     | "fn_threshold()"
                     | "fn_DOMAIN_SEPARATOR()"
                     | "fn_allSigners()"
                     | "fn_constructor" "(" Int "," LstAddress ")"
                     | "fn_execute" "(" CallType
                                    "," Int
                                    "," Int
                                    "," Address
                                    "," Data
                                    "," "[" LstSig "]" ")"

  syntax FnLog ::= "{" "fn:"        FnDetails
                   "," "callvalue:" Int
                   "," "callgas:"   Int "}"

  syntax CallLog ::= "{" "op:"   CallType
                     "," "gas:"  Int
                     "," "val:"  Int
                     "," "dst:"  Address
                     "," "data:" Data "}"

  syntax RetVal ::= ".RetVal"
                  | Int
                  | Bool
                  | String
                  | Set
                  | LstAddress

  // --- Utils ---

  syntax LstSignedMsg ::= "#take" Int LstSignedMsg [function]
  rule #take _ .LstSignedMsg => .LstSignedMsg
  rule #take 0 _             => .LstSignedMsg
  rule #take N ( X : XS )    => X : ( #take (N -Int 1) XS )
    requires N >Int 0

  syntax Int ::= "#len" LstAddress  [function]
  rule #len .LstAddress => 0
  rule #len ( _ : XS ) => 1 +Int ( #len XS )

  syntax Set ::= "#toSet" LstAddress [function]
  rule #toSet .LstAddress => .Set
  rule #toSet X : XS => SetItem(X) ( #toSet XS )

  syntax Int ::= "pow8"   // 2 ^ 8
               | "pow256" // 2 ^ 256
  rule pow8   => 256 [macro]
  rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936 [macro]

  // the overhead required to check that gas remaing >= gas to send with call
  syntax Int ::= "gasCheckOverhead"
  rule gasCheckOverhead => 2  [macro]

endmodule
