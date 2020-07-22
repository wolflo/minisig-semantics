requires "syntax.k"
requires "types.k"

module MINISIG
  imports DOMAINS
  imports MINISIG-SYNTAX
  imports MINISIG-TYPES

  configuration
    <msig>
      <k>  $PGM:Exp </k>
      <this>
        <nonce> 1:Int </nonce>
        <domSep> 2:Int </domSep>
        <threshold> 3:Int </threshold>
        <balance> 4:Int </balance>
        <signers> SetItem(1) SetItem(2) SetItem(3) </signers>
      </this>
      // mapping from signature to the address that should be recovered
      <ecrecover> .Map </ecrecover>
      <return> .K </return>
    </msig>

  // revert takes an error and consumes remaining operations
  syntax KItem ::= "#revert" Error
  rule <k> #revert _ERROR ~> (_:Exp => .K) ...</k>

  // sequence expressions
  rule E1:Exp E2:Exp => E1 ~> E2      [simplification]

  // --- View Functions ---

  // nonce()
  rule
    <k> View ( Nonce ) => . ...</k>
    <nonce> NONCE </nonce>
    <return> _ => NONCE </return>

  // threshold()
  rule
    <k> View ( Thresh ) => .K ...</k>
    <threshold> THRESH </threshold>
    <return> _ => THRESH </return>

  // DOMAIN_SEPARATOR()
  rule
    <k> View ( DomSep ) => .K ...</k>
    <domSep> DOMSEP </domSep>
    <return> _ => DOMSEP </return>

  // allSigners()
  rule
    <k> View ( Signers ) => .K ...</k>
    <signers> SIGNERS </signers>
    <return> _ => SIGNERS </return>

endmodule
