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

  rule [split]: split(vpair(V1,V2), X1 . X2 . M) => M[V1 / X1][V2 / X2]

  rule [casel]: case(inl(V), X1 . M1, _  . _ ) => M1[V / X1]
  rule [caser]: case(inr(V), _  . _ , X2 . M2) => M2[V / X2]

  rule [force]: {M}! => M

  rule [let]: let X = return(V) in M => M[V / X]

  rule [apply]: (\ X . M) V => M[V / X]

  rule [fst]: fst(cpair(M,_)) => M
  rule [snd]: snd(cpair(_,M)) => M
endmodule