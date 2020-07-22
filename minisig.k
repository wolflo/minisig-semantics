requires "syntax.k"
requires "types.k"

module MINISIG
  imports MINISIG-SYNTAX
  imports MINISIG-TYPES

  configuration
    <msig>
      <k>  $PGM:Tx </k>
      <call>
        <callvalue> 12:Int </callvalue>
        <return> .K </return>
      </call>
      <msig-state>
        <nonce> 1:Int </nonce>
        <domSep> 2:Int </domSep>
        <threshold> 3:Int </threshold>
        <balance> 4:Int </balance>
        <signers> SetItem(1) SetItem(2) SetItem(3) </signers>
      </msig-state>
      <prestate> .K </prestate>
      <fn-log> .List </fn-log> // functions that are run on this contract
      <call-log> .List </call-log>  // calls made from this contract
      // mapping from signature to the address that should be recovered
      <ecrecover> .Map </ecrecover>
    </msig>

  // sequence expressions
  rule E1:Exp E2:Exp => E1 ~> E2                      [simplification]
  rule T1:Tx T2:Tx => T1 ~> T2                        [simplification]
  rule sendTx E:Exp => #pushState ~> E ~> #dropState  [simplification]


  // halt takes an error and consumes remaining operations
  syntax KItem ::= "#halt" Error
  rule <k> #halt _ERROR ~> (_:Exp => .K) ...</k>

  // Function completion -- revert or finalize
  syntax OpInternal ::= "#revert" Error
                      | "#finalize" FnDetails

  rule <k> #revert ERROR => #popState ~> #halt ERROR ...</k>

  rule
    <k> #finalize FN => . ...</k>
    <callvalue> CALLVAL </callvalue>
    <return> RET </return>
    <fn-log>
      ...
      (.List => ListItem( { fn: FN, callvalue: CALLVAL, return: RET } ))
    </fn-log>

  syntax OpInternal ::= "#pushState"
                      | "#popState"
                      | "#dropState"
  rule
    <k> #pushState => . ...</k>
    <msig-state> STATE </msig-state>
    <prestate> _ => STATE </prestate>

  rule
    <k> #popState => . ...</k>
    <msig-state> _ => STATE </msig-state>
    <prestate> STATE => .K </prestate>

  rule
    <k> #dropState => . ...</k>
    <prestate> _ => .K </prestate>

  // --- View Functions ---

  // not payable
  rule
    <k> View ( _ ) => #revert INVALID_CALLVAL ...</k>
    <callvalue> CALLVAL </callvalue>
    <return> _ => . </return>
  requires notBool CALLVAL ==Int 0

  // nonce()
  rule
    <k> View ( Nonce ) => #finalize nonce ...</k>
    <callvalue> CALLVAL </callvalue>
    <nonce> NONCE </nonce>
    <return> _ => NONCE </return>
  requires CALLVAL ==Int 0

  // threshold()
  rule
    <k> View ( Thresh ) => #finalize threshold ...</k>
    <callvalue> CALLVAL </callvalue>
    <threshold> THRESH </threshold>
    <return> _ => THRESH </return>
  requires CALLVAL ==Int 0

  // DOMAIN_SEPARATOR()
  rule
    <k> View ( DomSep ) => #finalize DOMAIN_SEPARATOR ...</k>
    <callvalue> CALLVAL </callvalue>
    <domSep> DOMSEP </domSep>
    <return> _ => DOMSEP </return>
  requires CALLVAL ==Int 0

  // allSigners()
  rule
    <k> View ( Signers ) => #finalize allSigners ...</k>
    <callvalue> CALLVAL </callvalue>
    <signers> SIGNERS </signers>
    <return> _ => SIGNERS </return>
  requires CALLVAL ==Int 0

endmodule
