requires "substitution.md"

module HANDLER-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "vunit"
               | "vpair" "(" Val "," Val ")"
               | "inl" "(" Val ")"
               | "inr" "(" Val ")"
               | "{" Comp "}"
               | "(" Val ")" [bracket]


  syntax Comp ::= "split" "(" Val "," SplitFst ")"
                | "case0" "(" Val ")"
                | "case" "(" Val "," CaseL "," CaseR ")"
                | Val "!"
                | "return" "(" Val ")"
                | "let" KVar "=" Comp "in" Comp
                | "\\" KVar "." Comp  [binder]
                | Comp Val
                | "cunit"
                | "cpair" "(" Comp "," Comp ")"
                | "fst" "(" Comp ")"
                | "snd" "(" Comp ")"
                | "(" Comp ")" [bracket]
    
    syntax SplitFst ::= KVar "." SplitSnd [binder]
    syntax SplitSnd ::= KVar "." Comp [binder]

    syntax CaseL ::= KVar "." Comp [binder]
    syntax CaseR ::= KVar "." Comp [binder]

endmodule

module HANDLER
  imports HANDLER-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult ::= Comp

  configuration <T>
                <k> $PGM:Comp</k>
                </T>

  rule [split]: split(vpair(V1:Val,V2:Val), X1:KVar . X2:KVar . M:Comp) =>
         M[V1 / X1][V2 / X2]

  rule [casel]: case(inl(V:Val), X1:KVar . M1:Comp, _:KVar . _:Comp) =>
         M1[V / X1]
  rule [caser]: case(inr(V:Val), _:KVar . _:Comp, X2:KVar . M2:Comp) =>
         M2[V / X2]

  rule [force]: {M}! => M

// ---------- Let ----------
  syntax Bool ::= isReturn(K) [function, symbol]
  rule isReturn(return(_:Val):Comp) => true
  rule isReturn(_) => false [owise]

  syntax Comp ::= letFrame(KVar, Comp)
  rule [letPush]: let X:KVar = M1:Comp in M2:Comp => M1 ~> letFrame(X, M2)
       requires notBool isReturn(M1) 
  rule [letPop]: M1 ~> letFrame(X, M2) => let X = M1 in M2
       requires isReturn(M1)
  rule [letBeta]: let X:KVar = return(V:Val) in M => M[V / X]
// ---------- Let ----------

// ---------- Apply ----------
  syntax Bool ::= isLambda(K) [function, symbol]
  rule isLambda((\ _ . _):Comp) => true
  rule isLambda(_) => false [owise]

  syntax Comp ::= applyFrame(Val)
  rule [applyPush]: M:Comp V:Val => M ~> applyFrame(V)
       requires notBool isLambda(M)
  rule [applyPop]: M ~> applyFrame(V) => M V
       requires isLambda(M)
  rule [applyBeta]: (\ X:KVar . M:Comp) V:Val => M[V / X]
// ---------- Apply ----------

// ---------- Projections ----------
  syntax Bool ::= isCPair(K) [function, symbol]
  rule isCPair(cpair(_,_):Comp) => true
  rule isCPair(_) => false [owise]

  syntax Comp ::= "fstFrame" | "sndFrame"
  rule [fstPush]: fst(M) => M ~> fstFrame
       requires notBool isCPair(M)
  rule [fstPop]: M ~> fstFrame => fst(M)
       requires isCPair(M)
  rule [fstBeta]: fst(cpair(M:Comp,_:Comp)) => M
  rule [sndPush]: snd(M) => M ~> sndFrame
       requires notBool isCPair(M)
  rule [sndPop]: M ~> sndFrame => snd(M)
       requires isCPair(M)
  rule [sndBeta]: snd(cpair(_:Comp,M:Comp)) => M
// ---------- Projections ----------
endmodule