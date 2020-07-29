requires "syntax.k"
requires "types.k"

// TODO
// - constructor
// - testing harness
// - would be nice if reverted fn still added to fn-log
module MINISIG
  imports MINISIG-SYNTAX
  imports MINISIG-TYPES

  configuration
    <msig>
      <k>  $PGM:Tx </k>

      <call>
        <callvalue> 0:Int </callvalue>
        <returndata> .RetVal </returndata>
        <status> .Status </status>
      </call>

      <msig-state>
        <nonce> 1:Int </nonce>
        <domSep> 2:Int </domSep>
        <threshold> 2:Int </threshold>
        <balance> 4:Int </balance>
        <signers> SetItem(55) SetItem(56) SetItem(3) SetItem(0) </signers>
      </msig-state>

      <prestate> .K </prestate>
      <fn-log> .List </fn-log> // functions that are run on this contract
      <return-log> .List </return-log> // data returned from this contract
      <call-log> .List </call-log>  // calls made from this contract

      <world>
        <ecrecover>
          {sig:"foo1", nonce:1, op:Call, val:1, dst:77, data:"data1"} |-> 55
          {sig:"bar1", nonce:1, op:Call, val:1, dst:77, data:"data1"} |-> 56
          {sig:"foo2", nonce:2, op:Call, val:1, dst:77, data:"data2"} |-> 55
          {sig:"bar2", nonce:2, op:Call, val:1, dst:77, data:"data2"} |-> 56
        </ecrecover> // signature => signer
        <call-success> ListItem(true) ListItem(true) </call-success>
        <codesize> .Map </codesize>  // address => codesize
      </world>

    </msig>

  // --- sequence expressions ---
  rule E1:Exp E2:Exp => E1 ~> E2                        [simplification]
  rule T1:Tx T2:Tx   => T1 ~> T2                        [simplification]
  rule sendTx E:Exp  => #pushState ~> E ~> #dropState   [simplification]

  // --- log function calls ---
  rule
    <k> #log FN => . ...</k>
    <callvalue> CALLVAL </callvalue>
    <fn-log> (.List => ListItem( { fn: FN, callvalue: CALLVAL } )) ...</fn-log>

  // --- function resolution ---

  // halt takes an error and consumes remaining operations
  syntax KItem ::= "#halt" Error
  rule <k> #halt _ERROR ~> (_:Exp => .K)        ...</k>
  rule <k> #halt _ERROR ~> (_:OpInternal => .K) ...</k>

  syntax OpInternal ::= "#revert" Error
                      | "#return" RetVal
                      | "#finalize"

  rule
    <k> #revert ERROR => #popState ~> #halt ERROR ...</k>
    <status> _ => MSIG_REVERT </status>
    <returndata> _ => .RetVal </returndata>

  rule
    <k> #return RETVAL => . ...</k>
    <callvalue> _ => 0 </callvalue>
    <returndata> _ => RETVAL </returndata>
    <return-log> (.List => ListItem ( RETVAL )) ...</return-log>

  // finalize successful execution by setting status
  rule
    <k> #finalize => . ...</k>
    <status> _ => MSIG_SUCCESS </status>

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
  // ---------------

  syntax OpInternal ::= "#exec" CallType Int Address Data LstSignedMsg

  rule
    <k> Exec ( OP , VAL , DST , DATA , SIGS )
      => #exec OP VAL DST DATA ( #toLstSignedMsg OP VAL DST DATA NONCE SIGS )
      ~> #finalize
    ...
    </k>
    <nonce> NONCE </nonce>

  rule
    <k> #exec OP VAL DST DATA SMSGS
      => #checkPrestate OP VAL DST SMSGS
      ~> #mkCall OP VAL DST DATA
      ~> #checkPoststate OP ( NONCE +Int 1 )
      ~> #return true
    ...
    </k>
    <callvalue> CALLVAL </callvalue>
    <nonce> NONCE => NONCE +Int 1 </nonce>
    <balance> BAL => BAL +Int CALLVAL </balance>
  requires
    (NONCE +Int 1) <Int pow256 // behavior unsepcified if nonce + 1 >= pow256
    andBool (BAL +Int CALLVAL) <Int pow256

  // --- validate initial state ---
  syntax OpInternal ::= OpRequire
  syntax OpRequire ::= "#checkPrestate" CallType Int Address LstSignedMsg

  rule
    <k> #checkPrestate OP VAL DST SMSGS
      => #checkVal VAL
      ~> #checkDst OP DST
      ~> #checkSigs ( #take THRESH SMSGS )
    ...
    </k>
    <threshold> THRESH </threshold>


  // -- balance must be sufficient for call
  syntax OpRequire ::= "#checkVal" Int

  rule
    <k> #checkVal VAL => #revert INVALID_VAL ...</k>
    <balance> BAL </balance>
  requires VAL >Int BAL

  rule
    <k> #checkVal VAL => . ...</k>
    <balance> BAL </balance>
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
    <k> #checkDst DelegateCall DST => #revert DELEGATECALL_DST_EMPTY_CODE ...</k>
    <codesize>... DST |-> CSIZE ...</codesize>
  requires CSIZE ==Int 0

  // dst address is not in codesize mapping, defaults to 0
  rule
    <k> #checkDst DelegateCall DST => #revert DELEGATECALL_DST_EMPTY_CODE ...</k>
    <codesize> CSIZES </codesize>
  requires notBool (DST in_keys(CSIZES))

  // --- validate signatures ---
  syntax OpRequire ::= "#checkSigs" LstSignedMsg

  rule
    <k> #checkSigs SMSGS
      => #checkNonzeroHead ( #ecrec RHO SMSGS )
      ~> #checkAscOrder ( #ecrec RHO SMSGS )
      ~> #checkSizeCap THRESH SIGNERS ( #toSet ( #ecrec RHO SMSGS ) )
    ...
    </k>
    <ecrecover> RHO </ecrecover>
    <signers> SIGNERS </signers>
    <threshold> THRESH </threshold>

  // -- recover signatures
  syntax LstAddress ::= "#ecrec" Map LstSignedMsg [function]

  rule #ecrec _ .LstSignedMsg => .LstAddress

  rule #ecrec RHO:Map ( SMSG : SMSGS )
    => { RHO [ SMSG ] orDefault 0 }:>Address : ( #ecrec RHO SMSGS )

  // -- check that the first recovered signer > 0
  syntax OpRequire ::= "#checkNonzeroHead" LstAddress

  rule #checkNonzeroHead X : _ => .K requires X >Int 0

  // TODO: specify this more completely
  rule #checkNonzeroHead .LstAddress => #revert EMPTY_SIGNERS
  rule #checkNonzeroHead X : _       => #revert ZERO_ADDRESS_SIGNER
    requires X ==Int 0

  // -- require recovered signers to be in ascending order
  syntax OpRequire ::= "#checkAscOrder" LstAddress

  rule #checkAscOrder _ : .LstAddress  => .

  rule #checkAscOrder X1 : X2 : XS => #checkAscOrder X2 : XS
    requires X1 <Int X2

  rule #checkAscOrder X1 : X2 : _  => #revert SIGS_UNORDERED
    requires X1 >=Int X2

  // -- assert | recovered_signers \intersect signers | >= threshold
  syntax OpRequire ::= "#checkSizeCap" Int Set Set

  rule #checkSizeCap N S1 S2 => .K
    requires size ( intersectSet ( S1 , S2 ) ) >=Int N

  rule #checkSizeCap N S1 S2 => #revert INSUFFICIENT_VALID_SIGS
    requires size ( intersectSet ( S1 , S2) ) <Int N

  // --- make external call ---
  syntax OpInternal ::= "#mkCall" CallType Int Address Data
  rule
    <k> #mkCall OP VAL DST DATA => . ...</k>
    <call-log>
      .List => ListItem( { op:OP, val:VAL, dst:DST, data:DATA } )
    ...
    </call-log>
    <balance> BAL => BAL -Int VAL </balance>
  requires BAL >=Int VAL // this should always hold at this point

  // --- check result of call and nonce (if delegatecall) ---
  syntax OpRequire ::= "#checkPoststate" CallType Int
  // - assert call succeeded
  // - if delegatecall, assert that nonce is unchanged from before call

  // call_success /\ op == delegate_call => nonce_unchanged
  // call_success /\ not(op == delegate_call) \/ nonce_unchanged
  rule
    <k> #checkPoststate OP NONCE_PRECALL => . ...</k>
    <call-success> ( ListItem ( CALLRET ) => .List ) ...</call-success>
    <nonce> NONCE_POSTCALL </nonce>
  requires
    CALLRET ==Bool true
    andBool ( notBool OP ==K DelegateCall
              orBool NONCE_POSTCALL ==Int NONCE_PRECALL )

  rule
    <k> #checkPoststate OP NONCE_PRECALL => #revert INVALID_POSTSTATE ...</k>
    <nonce> NONCE_POSTCALL </nonce>
  requires
    OP ==K DelegateCall
    andBool notBool NONCE_POSTCALL ==Int NONCE_PRECALL

  rule
    <k> #checkPoststate _ _ => #revert CALL_FAILED ...</k>
    <call-success> ListItem(CALLRET) ...</call-success>
  requires CALLRET ==Bool false

  // an empty call-success list is assumed to be false
  rule
    <k> #checkPoststate _ _ => #revert CALL_FAILED ...</k>
    <call-success> .List </call-success>


  // --- View Functions ---
  // ----------------------

  // not payable
  rule
    <k> View ( _ ) => #revert INVALID_CALLVAL ...</k>
    <callvalue> CALLVAL </callvalue>
  requires notBool CALLVAL ==Int 0

  // nonce()
  rule
    <k> View ( Nonce )
      => #return NONCE
      ~> #finalize
    ...
    </k>
    <callvalue> CALLVAL </callvalue>
    <nonce> NONCE </nonce>
  requires CALLVAL ==Int 0

  // threshold()
  rule
    <k> View ( Thresh )
      => #return THRESH
      ~> #finalize
    ...
    </k>
    <callvalue> CALLVAL </callvalue>
    <threshold> THRESH </threshold>
  requires CALLVAL ==Int 0

  // DOMAIN_SEPARATOR()
  rule
    <k> View ( DomSep )
      => #return DOMSEP
      ~> #finalize
    ...
    </k>
    <callvalue> CALLVAL </callvalue>
    <domSep> DOMSEP </domSep>
  requires CALLVAL ==Int 0

  // allSigners()
  rule
    <k> View ( Signers )
      => #return SIGNERS
      ~> #finalize
    ...
    </k>
    <callvalue> CALLVAL </callvalue>
    <signers> SIGNERS </signers>
  requires CALLVAL ==Int 0

endmodule
