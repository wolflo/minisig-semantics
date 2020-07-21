module MINISIG-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Uint ::= Int
  syntax Address ::= Int
  syntax CallType ::= "Call" | "DelegateCall"
  syntax Data ::= ".Data" | Int
  syntax Sig ::= Int

  syntax LstSig ::= List{Sig, ","}
  syntax LstAddress ::= List{Address, ","}

  syntax FnView ::= "nonce" "(" ")"
                  | "threshold" "(" ")"
                  | "DOMAIN_SEPARATOR" "(" ")"
                  | "allSigners" "(" ")"

  syntax FnExec ::= "execute" "(" CallType "," Uint "," Address "," Data "," "[" LstSig "]" ")"

  syntax Exp ::= left:
                 FnView
               | FnExec
               | Exp Exp
  /* execute(CallType _callType
            , uint256 _value
            , address _target
            , bytes calldata _data
            , bytes calldata _sigs)
            payable returns (bool) */

endmodule
