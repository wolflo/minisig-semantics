module MINISIG-SYNTAX
  imports DOMAINS-SYNTAX

  syntax CallType ::= "Call" | "DelegateCall"
  syntax Sig ::= String
  syntax Data ::= String
  syntax Address ::= Int

  syntax LstSig ::= List{Sig, ","}

  syntax FnView ::= "nonce" "(" ")"
                  | "threshold" "(" ")"
                  | "DOMAIN_SEPARATOR" "(" ")"
                  | "allSigners" "(" ")"

  syntax FnExec ::= "execute" "(" CallType "," Int "," Address "," Data "," "[" LstSig "]" ")"

  syntax Exp ::= FnView
               | FnExec
               | Exp Exp  [left]

  syntax Tx ::= "sendTx" Exp
              | Tx Tx     [left]

  /* execute(CallType _callType
            , uint256 _value
            , address _target
            , bytes calldata _data
            , bytes calldata _sigs)
            payable returns (bool) */

endmodule
