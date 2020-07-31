module MINISIG-SYNTAX
  imports DOMAINS-SYNTAX

  syntax CallType ::= "Call" | "DelegateCall"
  syntax Sig      ::= String
  syntax Data     ::= String
  syntax Address  ::= Int

  syntax LstSig     ::= List{Sig, ":"}
  syntax LstAddress ::= List{Address, ":"}


  syntax Opt ::= "value:" Int
  /* syntax FnOpt ::= "{" Opt "}" */

  syntax FnView     ::= "nonce"
                      | "threshold"
                      | "DOMAIN_SEPARATOR"
                      | "allSigners"
  syntax ViewParams ::= "(" ")"

  syntax FnExec     ::= "execute"
  syntax ExecParams ::= "(" CallType
                        "," Int
                        "," Address
                        "," Data
                        "," "[" LstSig "]" ")"

  syntax FnCstr     ::= "constructor"
  syntax CstrParams ::= "(" Int "," "[" LstAddress "]" ")"



  /* execute(CallType _callType
            , uint256 _value
            , address _target
            , bytes calldata _data
            , bytes calldata _sigs)
            payable returns (bool) */
  /* syntax FnExec ::= "execute" "(" CallType */
  /*                                   "," Int */
  /*                                   "," Address */
  /*                                   "," Data */
  /*                                   "," "[" LstSig "]" ")" */


  syntax Fn ::= FnView
              | FnExec
              | FnCstr

  syntax Params ::= ViewParams
                  | ExecParams
                  | CstrParams

  syntax Exp ::= Fn Params
               | Fn "{" Opt "}" Params
               | Exp Exp  [left]

  syntax Tx ::= "sendTx" Exp
              | Tx Tx     [left]

endmodule
