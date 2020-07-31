module MINISIG-SYNTAX
  imports DOMAINS-SYNTAX

  syntax CallType ::= "Call" | "DelegateCall"
  syntax Sig      ::= String
  syntax Data     ::= String
  syntax Address  ::= Int

  syntax LstSig     ::= List{Sig, ":"}
  syntax LstAddress ::= List{Address, ":"}


  syntax Opt ::= "value:" Int

  syntax FnView     ::= "nonce"
                      | "threshold"
                      | "DOMAIN_SEPARATOR"
                      | "allSigners"
  syntax ViewParams ::= "(" ")"

  syntax FnExec     ::= "execute"
  syntax ExecParams ::= "(" CallType                // call or delegatecall
                        "," Int                     // gas to send with call
                        "," Int                     // value to send with call
                        "," Address                 // destination of call
                        "," Data                    // data to send with call
                        "," "[" LstSig "]" ")"      // list of signatures

  syntax FnCstr     ::= "constructor"
  syntax CstrParams ::= "(" Int                     // threshold
                        "," "[" LstAddress "]" ")"  // list of signers

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
