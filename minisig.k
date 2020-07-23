requires "syntax.k"
requires "types.k"

// TODO add method for asserting invariants
module MINISIG
  imports MINISIG-SYNTAX
  imports MINISIG-TYPES

  configuration
    <msig>
      <k>  $PGM:Tx </k>
      <call>
        <callvalue> 0:Int </callvalue>
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
      <world>
        <ecrecover> .Map </ecrecover> // signature => signer
        <codesize> .Map </codesize>  // address => codesize
      </world>
    </msig>

  // --- sequence expressions ---
  rule E1:Exp E2:Exp => E1 ~> E2                      [simplification]
  rule T1:Tx T2:Tx => T1 ~> T2                        [simplification]
  rule sendTx E:Exp => #pushState ~> E ~> #dropState  [simplification]

  // --- function resolution ---

  // halt takes an error and consumes remaining operations
  syntax KItem ::= "#halt" Error
  rule <k> #halt _ERROR ~> (_:Exp => .K) ...</k>
  rule <k> #halt _ERROR ~> (_:OpInternal => .K) ...</k>

  syntax OpInternal ::= "#revert" Error
                      | "#finalize" FnDetails

  rule <k> #revert ERROR => #popState ~> #halt ERROR ...</k>

  // finalize a successful execution by logging the function
  rule
    <k> #finalize FN => . ...</k>
    <callvalue> CALLVAL </callvalue>
    <return> RET </return>
    <fn-log>
      ...
      (.List => ListItem( { fn: FN, callvalue: CALLVAL, return: RET } ))
    </fn-log>

  // --- state rollbacks ---

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


  // --- Execute ---

  syntax OpInternal ::= "#checkPoststate"
                      | "#mkCall" CallType Int Address Data
                      | OpRequire

  syntax OpRequire ::= "#checkSigs" CallType Int Address Data List
                     | "#checkSigsLen" List
                     | "#checkSigsOrder" List

  rule
    <k> Exec ( OP, VAL, DST, DATA, SIGS )
      => #checkPrestate OP VAL DST DATA SIGS
      ~> #mkCall OP VAL DST DATA
      ~> #checkPoststate
    ...
    </k>
    <nonce> NONCE => NONCE +Int 1 </nonce>
  requires (NONCE +Int 1) <Int pow256

  syntax OpInternal ::= "#checkPrestate" CallType Int Address Data List

  // TODO:
  // #checkSigs => #checkSigsLen ~> #checkSigsOrder ~> #getMsg ~> #ecrecover
  /* rule #checkPrestate Call _ _ _ _ => #revert UNSPECIFIED */
  /* rule <k> #checkPrestate DelegateCall _ _ _ _ => .K ...</k> */
  rule
    <k> #checkPrestate OP VAL DST DATA SIGS
      => #checkVal VAL
      ~> #checkDst OP DST
      ~> #checkSigs OP VAL DST DATA SIGS
    ...
    </k>

  // -- balance must be sufficient for call

  syntax OpRequire ::= "#checkVal" Int

  rule
    <k> #checkVal VAL => #revert INVALID_VAL ...</k>
    <balance> BAL </balance>
    <return> _ => . </return>
  requires VAL >Int BAL

  rule
    <k> #checkVal VAL => . ...</k>
    <balance> BAL </balance>
    <return> _ => . </return>
  requires notBool VAL >Int BAL

  // -- delegatecall requires that codesize(dstAddress) > 0

  syntax OpRequire ::= "#checkDst" CallType Address

  rule #checkDst Call _ => .K

  rule
    <k> #checkDst DelegateCall DST => . ...</k>
    <codesize>... DST |-> CSIZE ...</codesize>
  requires CSIZE >Int 0

  rule
    <k> #checkDst DelegateCall DST => #revert UNSPECIFIED ...</k>
    <codesize>... DST |-> CSIZE ...</codesize>
  requires notBool CSIZE >Int 0

  // dst address is not in codesize mapping, defaults to 0
  rule
    <k> #checkDst DelegateCall DST => #revert UNSPECIFIED ...</k>
    <codesize> CSIZES </codesize>
  requires notBool (DST in_keys(CSIZES))

  rule
    <k> #checkSigs OP VAL DST DATA SIGS
      => #checkSigsLen SIGS
      ~> #checkSigsOrder SIGS
    ...
    </k>

  rule
    <k> #checkSigsLen SIGS => . ...</k>
    <threshold> THRESH </threshold>
  requires
    size(SIGS) ==Int THRESH
    orBool size(SIGS) >Int THRESH

  rule
    <k> #checkSigsLen SIGS => #revert UNSPECIFIED ...</k>
    <threshold> THRESH </threshold>
  requires size(SIGS) <Int THRESH



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
