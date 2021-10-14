requires "substitution.md"

module HANDLERPRIME-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "()"
               | "(" Val "," Val ")"
               | "inl" "(" Val ")"
               | "inr" "(" Val ")"
               | "{" Comp "}"
               | "(" Val ")" [bracket]


  syntax Comp ::= "split" Val "with" SplitFst
                | "void" "(" Val ")"
                | "case" Val "of" "{" CaseL ";" CaseR "}"
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
    syntax Lambda ::= "\\" KVar "->" Comp  [binder]
    syntax CUnit ::= "<>"
    syntax CPair ::= "<" Comp "," Comp ">"

    syntax Canonical ::= Return | Lambda | CUnit | CPair

    syntax SplitFst ::= KVar "," SplitSnd [binder]
    syntax SplitSnd ::= KVar "->" Comp [binder]

    syntax CaseL ::= KVar "->" Comp [binder]
    syntax CaseR ::= KVar "->" Comp [binder]
endmodule

module HANDLERPRIME
  imports HANDLERPRIME-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult ::= Canonical

  configuration <T>
                <k> $PGM:Comp</k>
                </T>

  rule [split]: split (V1,V2) with X1, X2 -> M => M[V1 / X1][V2 / X2]

  rule [casel]: case inl(V) of { X1 -> M1 ; _  -> _  } => M1[V / X1]
  rule [caser]: case inr(V) of { _  -> _  ; X2 -> M2 } => M2[V / X2]

  rule [force]: {M}! => M

  rule [let]: let X = return(V) in M => M[V / X]

  rule [apply]: (\ X -> M) V => M[V / X]

  rule [fst]: fst(< M, _ >) => M
  rule [snd]: snd(< _, M >) => M
endmodule