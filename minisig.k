requires "syntax.k"

module MINISIG
  imports DOMAINS
  imports MINISIG-SYNTAX

  configuration
    <msig>
      <k>  $PGM:Exp </k>
      <nonce> 1:Int </nonce>
      <domSep> 2:Int </domSep>
      <threshold> 3:Int </threshold>
      <balance> 4:Int </balance>
      <signers> ListItem(1) ListItem(2) ListItem(3) </signers>
      <return> .K </return>
    </msig>

  // revert takes an error and consumes remaining operations
  syntax Error ::= "ErrorCode1"
  syntax KItem ::= "#revert" Error
  rule <k> #revert _ERROR ~> (_:Exp => .K) ...</k>

  syntax ViewId ::= "Nonce"
                   | "Thresh"
                   | "DomSep"
                   | "Signers"
  syntax OpView ::= "View" ViewId
  syntax OpExec ::= "Exec" CallType Uint Address Data "[" LstSig "]"
  syntax Exp ::= OpView
               | OpExec

  // sequence expressions
  rule E1:Exp E2:Exp => E1 ~> E2      [simplification]

  rule nonce()            => View Nonce   [macro]
  rule threshold()        => View Thresh  [macro]
  rule allSigners()       => View Signers [macro]
  rule DOMAIN_SEPARATOR() => View DomSep  [macro]
  rule execute(TYPE, VAL, TO, DATA, [SIGS]) => Exec TYPE VAL TO DATA [SIGS] [macro]

  rule
    <k> View Nonce => . ...</k>
    <nonce> NONCE </nonce>
    <return> _ => NONCE </return>

  rule
    <k> View Thresh => .K ...</k>
    <threshold> THRESH </threshold>
    <return> _ => THRESH </return>

  rule
    <k> View DomSep => .K ...</k>
    <domSep> DOMSEP </domSep>
    <return> _ => DOMSEP </return>

  rule
    <k> View Signers => .K ...</k>
    <signers> SIGNERS </signers>
    <return> _ => SIGNERS </return>

endmodule
