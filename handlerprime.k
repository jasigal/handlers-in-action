requires "substitution.md"

module HANDLERPRIME-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX
  imports ID-SYNTAX

  syntax Val ::= KVar [color(red)]
               | "()" [color(red)]
               | "(" Val "," Val ")" [color(red)]
               | "inl" "(" Val ")" [color(red)]
               | "inr" "(" Val ")" [color(red)]
               | "thunk" "(" Comp ")" [color(red)]
               | "(" Val ")" [bracket, color(red)]

  syntax Comp ::= "split" Val "with" SplitFst [color(green)]
                | "void" "(" Val ")" [color(green)]
                | "case" Val "of" "{" CaseL ";" CaseR "}" [color(green)]
                | Val "!" [color(green)]
                | "let" KVar "=" Comp "in" Comp [strict(2), color(green)]
                | Comp Val [strict(1), color(green)]
                | "fst" "(" Comp ")" [strict, color(green)]
                | "snd" "(" Comp ")" [strict, color(green)]
                | "handle" Comp "with" HandlerBody [strict(1), color(green)]
                | "(" Comp ")" [bracket, color(green)]
    
    syntax Comp ::= Return
    syntax Comp ::= Lambda
    syntax Comp ::= CUnit
    syntax Comp ::= CPair
    syntax Comp ::= Op
    
    syntax Op ::= "[" Id "]" "(" Val "," OpBody ")" [color(blue)]
    syntax OpBody ::= "\\" KVar "->" Comp [binder, color(blue)]

    syntax HandlerBody ::= "{" HandlerReturn ";" HandlerOps "}" [color(green)]
    syntax HandlerReturn ::= "return" "(" KVar ")" "->" Comp [binder, color(green)]
    syntax HandlerOps ::= List{HandlerOp,";"} [color(green)]
    syntax HandlerOp ::= "[" Id "]" "(" HandlerOp1 [color(green)]
    syntax HandlerOp1 ::= KVar "," HandlerOp2 [binder, color(green)]
    syntax HandlerOp2 ::= KVar ")" "->" Comp [binder, color(green)]
    
    syntax Return ::= "return" "(" Val ")" [color(blue)]
    syntax Lambda ::= "lam" KVar "->" Comp  [binder, color(blue)]
    syntax CUnit ::= "<>" [color(blue)]
    syntax CPair ::= "<" Comp "," Comp ">" [color(blue)]

    syntax Canonical ::= Return | Lambda | CUnit | CPair | Op

    syntax SplitFst ::= KVar "," SplitSnd [binder, color(green)]
    syntax SplitSnd ::= KVar "->" Comp [binder, color(green)]

    syntax CaseL ::= KVar "->" Comp [binder, color(green)]
    syntax CaseR ::= KVar "->" Comp [binder, color(green)]
endmodule

module HANDLERPRIME
  imports HANDLERPRIME-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult ::= Canonical

  configuration <k> $PGM:Comp </k>

  rule [split]: split (V1,V2) with X1, X2 -> M => M[V1 / X1][V2 / X2]

  rule [casel]: case inl(V) of { X1 -> M1 ; _  -> _  } => M1[V / X1]
  rule [caser]: case inr(V) of { _  -> _  ; X2 -> M2 } => M2[V / X2]

  rule [force]: thunk(M:Comp)! => M

  rule [let]: let X = return(V) in M => M[V / X]
  rule [letOp]: let Y = [OP](V, \X -> M) in N => [OP](V, \X -> let Y = M in N)

  rule [apply]: (lam X -> M) V => M[V / X]
  rule [applyOp]: [OP](V, \X -> M) W => [OP](V, \X -> M W)

  rule [fst]: fst(< M, _ >) => M
  rule [fstOp]: fst([OP](V, \X -> M)) => [OP](V, \X -> fst(M))
  rule [snd]: snd(< _, M >) => M
  rule [sndOp]: snd([OP](V, \X -> M)) => [OP](V, \X -> snd(M))

  rule [handleVal]: handle return(V) with {return(X) -> M; _:HandlerOps}
                      => M[V / X]
  rule [handleOp]: (handle [OP](V, \X -> M) with {RET; OPS}):Comp
    => #fun(match(P, K, N)
              => N[V / P][thunk(lam X -> handle M with {RET; OPS}) / K]
           )(getOp(OP, OPS))

  syntax OpMatch ::= match(KVar, KVar, Comp)
  syntax OpMatch ::= getOp(Id, HandlerOps) [function]
                   | "getOpFailure"
  rule getOp(OP1:Id, [OP2](X, K) -> M ; _:HandlerOps) => match(X, K, M)
       requires OP1 ==K OP2
  rule getOp(OP1:Id, [OP2](_, _) -> _ ; OPS:HandlerOps) => getOp(OP1, OPS)
       requires OP1 =/=K OP2
  rule getOp(_:Id, .HandlerOps) => getOpFailure
endmodule