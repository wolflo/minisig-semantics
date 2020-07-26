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
        <threshold> 1:Int </threshold>
        <balance> 4:Int </balance>
        <signers> SetItem(1) SetItem(2) SetItem(3) </signers>
      </msig-state>
      <prestate> .K </prestate>
      <fn-log> .List </fn-log> // functions that are run on this contract
      <call-log> .List </call-log>  // calls made from this contract
      // mapping from signature to the address that should be recovered
      <world>
        <ecrecover> {sig:"foo", nonce:1, op:Call, val:1, dst:77, data:"data"} |-> "foo-addr" </ecrecover> // signature => signer
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

  syntax OpRequire ::= "#checkSigs" LstSignedMsg
                     | "#checkSigsLen" List
                     | "#checkSigsOrder" List

  syntax OpInternal ::= "#exec" CallType Int Address Data LstSignedMsg
  rule
    <k> Exec ( OP , VAL , DST , DATA , SIGS )
      => #exec OP VAL DST DATA ( #toLstSignedMsg OP VAL DST DATA NONCE SIGS )
    ...
    </k>
    <nonce> NONCE </nonce>

    rule 
      <k> #exec OP VAL DST DATA SMSGS
        => #checkPrestate OP VAL DST SMSGS
        ~> #mkCall OP VAL DST DATA
        ~> #checkPoststate
      ...
      </k>
      <nonce> NONCE => NONCE +Int 1 </nonce>
    requires (NONCE +Int 1) <Int pow256

  syntax OpInternal ::= "#checkPrestate" CallType Int Address LstSignedMsg

  rule
    <k> #checkPrestate OP VAL DST SMSGS
      => #checkVal VAL
      ~> #checkDst OP DST
      ~> #checkSigs SMSGS
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

  // dst for call op can be any -- incl. 0x0, msg.sender, address(this)
  rule #checkDst Call _ => .K

  rule
    <k> #checkDst DelegateCall DST => . ...</k>
    <codesize>... DST |-> CSIZE ...</codesize>
  requires CSIZE >Int 0

  rule
    <k> #checkDst DelegateCall DST => #revert UNSPECIFIED ...</k>
    <codesize>... DST |-> CSIZE ...</codesize>
  requires CSIZE ==Int 0

  // dst address is not in codesize mapping, defaults to 0
  rule
    <k> #checkDst DelegateCall DST => #revert UNSPECIFIED ...</k>
    <codesize> CSIZES </codesize>
  requires notBool (DST in_keys(CSIZES))

  rule
    <k> #checkSigs SMSGS
      => #ecrec RHO SMSGS
    ...
    </k>
    <ecrecover> RHO </ecrecover>

    syntax List ::= "#ecrec" Map LstSignedMsg [function]

    rule #ecrec _ .LstSignedMsg => .List

    rule #ecrec RHO ( SMSG , SMSGS )
      => ListItem( RHO [ SMSG ] ) ( #ecrec RHO SMSGS )
    requires SMSG in_keys(RHO)

    rule #ecrec RHO ( SMSG , SMSGS )
      => ListItem( 0 ) ( #ecrec RHO SMSGS )
    requires notBool SMSG in_keys(RHO)

    syntax SignedMsg ::= "#toSignedMsg" CallType Int Address Data Int Sig [function]

    rule #toSignedMsg OP VAL DST DATA NONCE SIG
      => { sig: SIG, nonce: NONCE, op: OP, val: VAL, dst: DST, data: DATA }

  rule
    <k> #checkSigsLen SIGS => . ...</k>
    <threshold> THRESH </threshold>
  requires
    size( SIGS ) ==Int THRESH
    orBool size( SIGS ) >Int THRESH

  rule
    <k> #checkSigsLen SIGS => #revert UNSPECIFIED ...</k>
    <threshold> THRESH </threshold>
  requires size( SIGS ) <Int THRESH


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
