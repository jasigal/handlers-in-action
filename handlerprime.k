requires "substitution.md"

module HANDLERPRIME-SYNTAX
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
                | Return
                | "let" KVar "=" Comp "in" Comp [strict(2)]
                | Lambda
                | Comp Val [strict(1)]
                | CUnit
                | CPair
                | "fst" "(" Comp ")" [strict]
                | "snd" "(" Comp ")" [strict]
                | "(" Comp ")" [bracket]
    
    syntax Return ::= "return" "(" Val ")"
    syntax Lambda ::= "\\" KVar "." Comp  [binder]
    syntax CUnit ::= "cunit"
    syntax CPair ::= "cpair" "(" Comp "," Comp ")"

    syntax Canonical ::= Return | Lambda | CUnit | CPair

    syntax SplitFst ::= KVar "." SplitSnd [binder]
    syntax SplitSnd ::= KVar "." Comp [binder]

    syntax CaseL ::= KVar "." Comp [binder]
    syntax CaseR ::= KVar "." Comp [binder]
endmodule

module HANDLERPRIME
  imports HANDLERPRIME-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult ::= Canonical

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

  rule [let]: let X:KVar = return(V:Val) in M => M[V / X]

  rule [apply]: (\ X:KVar . M:Comp) V:Val => M[V / X]

  rule [fst]: fst(cpair(M:Comp,_:Comp)) => M
  rule [snd]: snd(cpair(_:Comp,M:Comp)) => M
endmodule