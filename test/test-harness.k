requires "./test-harness-syntax.k"
requires "../minisig.k"

module TEST-HARNESS
  imports TEST-HARNESS-SYNTAX
  imports MINISIG

  configuration
    <k> $PGM:Test </k>

  // --- sequence expressions ---
  rule S:Setup T:Tx => S ~> T
  rule S1:Setup S2:Setup => S1 ~> S2

  syntax TestExp ::= StateExp
  rule setState SE:StateExp => #set SE
  rule #set SE1:StateExp SE2:StateExp => #set SE1 ~> #set SE2

  syntax TestExp ::= WorldExp
  rule setWorld WE:WorldExp => #set WE
  rule #set WE1:WorldExp WE2:WorldExp => #set WE1 ~> #set WE2

  syntax OpSet ::= "#set" TestExp

  // --- State setters ---

  rule
    <k> #set nonce := NONCE => . ...</k>
    <nonce> _ => NONCE </nonce>

  rule
    <k> #set balance := BAL => . ...</k>
    <balance> _ => BAL </balance>

  rule
    <k> #set threshold := THRESH => . ...</k>
    <threshold> _ => THRESH </threshold>

  rule
    <k> #set domSep := DOMSEP => . ...</k>
    <domSep> _ => DOMSEP </domSep>

  rule
    <k> #set signers := [ SIGNERS ] => . ...</k>
    <signers> _ => SIGNERS </signers>

  // --- World setters ---

  rule
    <k> #set gas-used-pre-call := GASUSED => . ...</k>
    <gas-used-pre-call> _ => GASUSED </gas-used-pre-call>

  rule
    <k> #set codesize [ ADDR ] := SIZE => . ...</k>
    <codesize>... ADDR |-> ( _ => SIZE ) ...</codesize>
  rule
    <k> #set codesize [ ADDR ] := SIZE => . ...</k>
    <codesize> RHO:Map ( .Map => ADDR |-> SIZE ) </codesize>
  requires notBool ADDR in_keys(RHO)

  rule
    <k> #set ecrecover [ SMSG ] := ADDR => . ...</k>
    <ecrecover>... SMSG |-> ( _ => ADDR ) ...</ecrecover>
  rule
    <k> #set ecrecover [ SMSG ] := ADDR => . ...</k>
    <ecrecover> RHO:Map ( .Map => SMSG |-> ADDR ) </ecrecover>
  requires notBool SMSG in_keys(RHO)

  rule
    <k> #set call-success := [ BOOLS ] => . ...</k>
    <call-success> _ => #fromLst BOOLS </call-success>

  // --- Utils ---

  syntax List ::= "#fromLst" LstBool  [function]
  rule #fromLst .LstBool => .List
  rule #fromLst ( B : BS ) => ListItem( B ) ( #fromLst BS )

endmodule
