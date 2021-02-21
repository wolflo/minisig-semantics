requires "types.k"

// TODO
// - fallback function
// - rewrites that arent a step but involve sequencing
module MINISIG
  imports MINISIG-TYPES

  configuration
    <msig>
      <k> $PGM:Tx </k>
      <status> .Status </status>

      <msig-state>
        <nonce> 0:Int </nonce>
        <domSep> "" </domSep>
        <threshold> 0:Int </threshold>
        <balance> 0:Int </balance>
        <signers> .LstAddress </signers>
      </msig-state>

      <call>
        <caller> 0:Address </caller>
        <callvalue> 0:Int </callvalue>
        <callgas> 0:Int </callgas>
        <returndata> .RetVal </returndata>
      </call>

      <log>
        <fn-log> .List </fn-log> // functions that are run on this contract
        <return-log> .List </return-log> // data returned from this contract
        <call-log> .List </call-log>  // calls made from this contract
      </log>

      <prestate> .K </prestate> // used internally for state rollback

      <world>
        <ecrecover> .Map </ecrecover> // signature => signer
        <call-success> .List </call-success>
        <gas-used-pre-call> 0:Int </gas-used-pre-call>
      </world>

    </msig>


  // --- sequence expressions ---
  rule E1:Exp E2:Exp => E1 ~> E2
  rule T1:Tx T2:Tx   => T1 ~> T2
  rule sendTx E:Exp  => #pushState ~> E ~> #dropState

  // --- log function calls ---
  rule
    <k> #log FN => . ...</k>
    <caller> CALLER </caller>
    <callgas> CALLGAS </callgas>
    <callvalue> CALLVAL </callvalue>
    <fn-log>
      (.List => ListItem( { fn: FN , caller: CALLER, callvalue: CALLVAL , callgas: CALLGAS } ))
    ...
    </fn-log>

  // --- set call prestate ---
  syntax OpSet ::= "#set1" Opt
  rule #set ( OPT , OPTS ) => #set1 OPT ~> #set OPTS
  rule #set .LstOpt => .K

  rule
    <k> #set1 ( value: VAL ) => .K ...</k>
    <callvalue> _ => VAL </callvalue>
  requires VAL >=Int 0 andBool VAL <Int pow256

  rule
    <k> #set1 ( gas: GAS ) => .K ...</k>
    <callgas> _ => GAS </callgas>
  requires GAS >=Int 0 andBool GAS <Int pow256

  rule
    <k> #set1 ( from: CALLER ) ...</k>
    <caller> _ => CALLER </caller>
  requires CALLER >Int 0 andBool CALLER <Int pow160

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

  syntax OpInternal ::= "#exec" AddressOrAny Address CallType Int Int Data LstSignedMsg

  rule
    <k> Exec ( SRC , DST , OP , GAS , VAL , DATA , SIGS )
      => #exec SRC DST OP GAS VAL DATA ( #toLstSignedMsg SRC DST OP GAS VAL DATA NONCE SIGS )
    ...
    </k>
    <nonce> NONCE </nonce>

  rule
    <k> #exec SRC DST OP GAS VAL DATA SMSGS
      => #checkPrestate SRC OP VAL SMSGS
      ~> #mkCall DST OP GAS VAL DATA
      ~> #checkPoststate
      ~> #return .RetVal
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
  syntax OpRequire ::= "#checkPrestate" AddressOrAny CallType Int LstSignedMsg

  rule
    <k> #checkPrestate SRC OP VAL SMSGS
      => #checkVal OP VAL
      ~> #checkSrc SRC
      ~> #checkSigs ( #take THRESH SMSGS )
    ...
    </k>
    <threshold> THRESH </threshold>
  requires THRESH >Int 0

  rule
    <k> #checkPrestate _ _ _ _ => #revert PRESTATE_THRESHOLD_ZERO ...</k>
    <threshold> 0 </threshold>

  // -- balance must be sufficient for call
  syntax OpRequire ::= "#checkVal" CallType Int

  // value is ignored for delegatecall
  rule #checkVal DelegateCall _ => .K

  rule
    <k> #checkVal Call VAL => #revert INVALID_VAL ...</k>
    <balance> BAL </balance>
  requires VAL >Int BAL

  rule
    <k> #checkVal Call VAL => . ...</k>
    <balance> BAL </balance>
  requires VAL <=Int BAL

  // -- caller must be approved to submit transaction --
  syntax OpRequire ::= "#checkSrc" AddressOrAny

  rule
    <k> #checkSrc SRC => . ...</k>
    <caller> CALLER </caller>
  requires SRC ==K CALLER orBool SRC ==K Any

  rule
    <k> #checkSrc SRC => #revert INVALID_CALLER ...</k>
    <caller> CALLER </caller>
  requires notBool (SRC ==K CALLER orBool SRC ==K Any)

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

  rule #checkAscOrder X1 : X2 : _  => #revert UNORDERED_SIGNERS
    requires X1 >=Int X2

  // -- assert | recovered_signers \intersect signers | >= threshold
  syntax OpRequire ::= "#checkSizeCap" Int LstAddress LstAddress

  rule #checkSizeCap N Lst1 Lst2 => .K
    requires size ( intersectSet ( #toSet Lst1 , #toSet Lst2 ) ) >=Int N

  rule #checkSizeCap N Lst1 Lst2 => #revert INSUFFICIENT_VALID_SIGS
    requires size ( intersectSet ( #toSet Lst1 , #toSet Lst2 ) ) <Int N

  // --- make external call ---
  syntax OpInternal ::= "#mkCall" Address CallType Int Int Data
  rule
    <k> #mkCall DST OP TXGAS VAL DATA => . ...</k>
    <call-log>
      .List => ListItem( { dst: DST
                         , op: OP
                         , gas: TXGAS
                         , val: VAL
                         , data: DATA } )
    ...
    </call-log>
    <callgas> CALLGAS </callgas>
    <balance> BAL => BAL -Int VAL </balance>
    <gas-used-pre-call> GASUSED </gas-used-pre-call>
  requires
    CALLGAS -Int GASUSED >=Int ( TXGAS +Int gasCheckOverhead )
    andBool BAL >=Int VAL // this should always hold at this point

  rule
    <k> #mkCall _ _ TXGAS _ _ => #revert INSUFFICIENT_CALLGAS ...</k>
    <callgas> CALLGAS </callgas>
    <gas-used-pre-call> GASUSED </gas-used-pre-call>
  requires CALLGAS -Int GASUSED <Int ( TXGAS +Int gasCheckOverhead )

  // --- check result of call ---
  syntax OpRequire ::= "#checkPoststate"
  rule
    <k> #checkPoststate => . ...</k>
    <call-success> ( ListItem( CALLRET ) => .List ) ...</call-success>
  requires CALLRET ==Bool true

  rule
    <k> #checkPoststate => #revert CALL_FAILED ...</k>
    <call-success> ListItem(CALLRET) ...</call-success>
  requires CALLRET ==Bool false

  // an empty call-success list is assumed to be false
  rule
    <k> #checkPoststate => #revert CALL_FAILED ...</k>
    <call-success> .List </call-success>


  // --- View Functions ---
  // ----------------------

  // not payable
  rule
    <k> View ( _ ) => #revert INVALID_CALLVAL ...</k>
    <callvalue> CALLVAL </callvalue>
  requires CALLVAL >Int 0

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
