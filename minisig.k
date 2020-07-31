requires "syntax.k"
requires "types.k"

// TODO
// - testing harness
// - fallback function
// - specify gas (but no deductions) -- if we have less than specified gas + {swap_cost}
//   at call time, revert
module MINISIG
  imports MINISIG-SYNTAX
  imports MINISIG-TYPES

  configuration
    <msig>
      <k>  $PGM:Tx </k>

      <msig-state>
        <nonce> 0:Int </nonce>
        <domSep> "" </domSep>
        <threshold> 0:Int </threshold>
        <balance> 4:Int </balance>
        <signers> .LstAddress </signers>
      </msig-state>

      <call>
        <callvalue> 0:Int </callvalue>
        <returndata> .RetVal </returndata>
        <status> .Status </status>
        <gas> 0:Int </gas>
      </call>

      <log>
        <fn-log> .List </fn-log> // functions that are run on this contract
        <return-log> .List </return-log> // data returned from this contract
        <call-log> .List </call-log>  // calls made from this contract
      </log>

      <prestate> .K </prestate> // used internally for state rollback

      <world>
        <ecrecover>
          {sig:"foo1", op:Call, nonce:0, gas:100, val:1, dst:77, data:"data1"} |-> 55
          {sig:"bar1", op:Call, nonce:0, gas:100, val:1, dst:77, data:"data1"} |-> 56
          {sig:"foo2", op:Call, nonce:0, gas:100, val:1, dst:77, data:"data2"} |-> 55
          {sig:"bar2", op:Call, nonce:0, gas:100, val:1, dst:77, data:"data2"} |-> 56
        </ecrecover> // signature => signer
        <call-success> ListItem(true) ListItem(true) </call-success>
        <codesize> .Map </codesize>  // address => codesize
        <gas-used-pre-call> 0:Int </gas-used-pre-call>
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

  // --- set call prestate ---
  rule
    <k> #set ( value: VAL ) => .K ...</k>
    <callvalue> _ => VAL </callvalue>
  requires VAL >=Int 0 andBool VAL <Int pow256

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
    <returndata> _ => RETVAL </returndata>
    <return-log> (.List => ListItem ( RETVAL )) ...</return-log>

  // finalize successful execution by setting status
  rule
    <k> #finalize => . ...</k>
    <status> _ => MSIG_SUCCESS </status>
    <callvalue> _ => 0 </callvalue>

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


  // --- Constructor ---
  // -------------------

  rule
    <k> Cstr ( THRESH , SIGNERS )
      => #checkNonzeroHead SIGNERS  // first signer cant be zero
      ~> #checkAscOrder SIGNERS     // check order of signers
      ~> #return .RetVal
      ~> #finalize
    ...
    </k>
    <callvalue> CALLVAL </callvalue>
    <nonce> _ => 0 </nonce>
    <domSep> _ => "domain_separator" </domSep> // TODO
    <threshold> _ => THRESH </threshold>
    <signers> _ => SIGNERS </signers>
    <balance> BAL => BAL +Int CALLVAL </balance>
  requires
    THRESH >Int 0 andBool THRESH <Int pow8
    andBool #len SIGNERS >=Int THRESH
    andBool (BAL +Int CALLVAL) <Int pow256 // alternative unspecified

  rule Cstr ( THRESH , _ ) => #revert INVALID_THRESHOLD
    requires
      THRESH ==Int 0
      orBool THRESH >=Int pow8

  rule Cstr ( THRESH , SIGNERS ) => #revert INSUFFICIENT_SIGNERS
    requires #len SIGNERS <Int THRESH


  // --- Execute ---
  // ---------------

  syntax OpInternal ::= "#exec" CallType Int Int Address Data LstSignedMsg

  rule
    <k> Exec ( OP , GAS , VAL , DST , DATA , SIGS )
      => #exec OP GAS VAL DST DATA ( #toLstSignedMsg OP GAS VAL DST DATA NONCE SIGS )
    ...
    </k>
    <nonce> NONCE </nonce>

  rule
    <k> #exec OP GAS VAL DST DATA SMSGS
      => #checkPrestate OP VAL DST SMSGS
      ~> #mkCall OP GAS VAL DST DATA
      ~> #checkPoststate OP ( NONCE +Int 1 )
      ~> #return true
      ~> #finalize
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
      ~> #checkSizeCap THRESH SIGNERS ( #ecrec RHO SMSGS )
    ...
    </k>
    <ecrecover> RHO </ecrecover>
    <signers> SIGNERS </signers>
    <threshold> THRESH </threshold>

  // -- recover signatures
  syntax LstAddress ::= "#ecrec" Map LstSignedMsg [function]

  rule #ecrec _ .LstSignedMsg => .LstAddress

  // ecrec returns 0 on failure
  rule #ecrec RHO:Map ( SMSG : SMSGS )
    => { RHO [ SMSG ] orDefault 0 }:>Address : ( #ecrec RHO SMSGS )

  // -- check that the first recovered signer > 0
  syntax OpRequire ::= "#checkNonzeroHead" LstAddress

  rule #checkNonzeroHead X : _ => .K requires X >Int 0

  // TODO: specify this more completely
  rule #checkNonzeroHead .LstAddress => #revert EMPTY_SIGNERS
  rule #checkNonzeroHead X : _       => #revert ZERO_ADDRESS_SIGNER
    requires X ==Int 0

  // -- require addresses to be in ascending order
  syntax OpRequire ::= "#checkAscOrder" LstAddress

  rule #checkAscOrder _ : .LstAddress  => .

  rule #checkAscOrder X1 : X2 : XS => #checkAscOrder X2 : XS
    requires X1 <Int X2

  rule #checkAscOrder X1 : X2 : _  => #revert SIGNERS_UNORDERED
    requires X1 >=Int X2

  // -- assert | recovered_signers \intersect signers | >= threshold
  syntax OpRequire ::= "#checkSizeCap" Int LstAddress LstAddress

  rule #checkSizeCap N Lst1 Lst2 => .K
    requires size ( intersectSet ( #toSet Lst1 , #toSet Lst2 ) ) >=Int N

  rule #checkSizeCap N Lst1 Lst2 => #revert INSUFFICIENT_VALID_SIGS
    requires size ( intersectSet ( #toSet Lst1 , #toSet Lst2 ) ) <Int N

  // --- make external call ---
  syntax OpInternal ::= "#mkCall" CallType Int Int Address Data
  rule
    <k> #mkCall OP GAS VAL DST DATA => . ...</k>
    <call-log>
      .List => ListItem( { op: OP
                         , gas: GAS
                         , val: #if OP ==K DelegateCall #then CALLVAL #else VAL #fi
                         , dst: DST
                         , data: DATA } )
    ...
    </call-log>
    <callvalue> CALLVAL </callvalue>
    <balance> BAL => BAL -Int VAL </balance>
  requires BAL >=Int VAL // this should always hold at this point

  // --- check result of call and nonce (if delegatecall) ---
  syntax OpRequire ::= "#checkPoststate" CallType Int
  // - assert call succeeded
  // - if delegatecall, assert that nonce is unchanged from before call

  // call_success /\ ( op == delegate_call => nonce_unchanged )
  // call_success /\ ( not(op == delegate_call) \/ nonce_unchanged )
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
