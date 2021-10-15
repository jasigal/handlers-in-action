requires "substitution.md"

module HANDLERPRIME-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX
  imports ID-SYNTAX

  // Values
  //
  // No values are strict as they do not compute.
  syntax Val ::= // Variables
                 KVar [color(red)]
                 // Value unit
               | "()" [color(red)]
                 // Value pairing
               | "(" Val "," Val ")" [color(red)]
                 // Left sum inclusion
               | "inl" "(" Val ")" [color(red)]
                 // Right sum inclusion
               | "inr" "(" Val ")" [color(red)]
                 // Suspend a computation
               | "thunk" "(" Comp ")" [color(red)]
                 // Brackets
               | "(" Val ")" [bracket, color(red)]

  // Computations
  //
  // Constructs which are strict in some component are also hoisting or
  // computation frames. For example, in the paper we see that
  //
  //     let x <- [] in N
  //
  // is a frame. Thus, let is strict in its second component.
  syntax Comp ::= // Split and bind a value pair
                  "split" Val "with" SplitFst [color(green)]
                  // Case match on the empty value
                | "void" "(" Val ")" [color(green)]
                  // Case match and bind on a sum value
                | "case" Val "of" "{" CaseL ";" CaseR "}" [color(green)]
                  // Force a suspended computation to continue
                | Val "!" [color(green)]
                  // Let binding
                | "let" KVar "=" Comp "in" Comp [strict(2), color(green)]
                  // Apply a computation to a value
                | Comp Val [strict(1), color(green)]
                  // Project from a pair of computations
                | "fst" "(" Comp ")" [strict, color(green)]
                | "snd" "(" Comp ")" [strict, color(green)]
                  // Handle a computation
                | "handle" Comp "with" HandlerBody [strict(1), color(green)]
                  // Brackets
                | "(" Comp ")" [bracket, color(green)]
    
    // We define canonical computations as separate sorts, and then subsort them
    // to the Comp sort. These are computations which have no semantic
    // transitions and no frames, and thus if they are at the head of our K cell
    // they should be put back into the frame they belong to. If there is no
    // parent cell, then the computation is over. This is Theorem 2 in the
    // paper.
    syntax Comp ::= Return
    syntax Comp ::= Lambda
    syntax Comp ::= CUnit
    syntax Comp ::= CPair
    syntax Comp ::= Op
    
    // Effect operations
    syntax Op ::= "[" Id "]" "(" Val "," OpBody ")" [color(blue)]
    syntax OpBody ::= "\\" KVar "->" Comp [binder, color(blue)]

    // Handler definitions
    //
    // A handler consists of one return matching case and then a list of
    // effect operation matching cases.
    syntax HandlerBody ::= "{" HandlerReturn ";" HandlerOps "}" [color(green)]
    // Return matching case
    syntax HandlerReturn ::= "return" "(" KVar ")" "->" Comp [binder, color(green)]
    // List of effect operation matchings
    syntax HandlerOps ::= List{HandlerOp,";"} [color(green)]
    // Effect operation matchings
    syntax HandlerOp ::= "[" Id "]" "(" HandlerOp1 [color(green)]
    syntax HandlerOp1 ::= KVar "," HandlerOp2 [binder, color(green)]
    syntax HandlerOp2 ::= KVar ")" "->" Comp [binder, color(green)]
    
    // Returns a value as a computation
    syntax Return ::= "return" "(" Val ")" [color(blue)]
    // Lambda abstraction over a computation
    syntax Lambda ::= "lam" KVar "->" Comp  [binder, color(blue)]
    // Unit type for computations
    syntax CUnit ::= "<>" [color(blue)]
    // Pair of computations
    syntax CPair ::= "<" Comp "," Comp ">" [color(blue)]

    // Canonical computations
    syntax Canonical ::= Return | Lambda | CUnit | CPair | Op

    // Binders for split
    syntax SplitFst ::= KVar "," SplitSnd [binder, color(green)]
    syntax SplitSnd ::= KVar "->" Comp [binder, color(green)]

    // Binders for case
    syntax CaseL ::= KVar "->" Comp [binder, color(green)]
    syntax CaseR ::= KVar "->" Comp [binder, color(green)]
endmodule

module HANDLERPRIME
  imports HANDLERPRIME-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  // The KResults (i.e. things which K will not rewrite and thus stops 
  // computation) are canonical terms since programs are computations.
  syntax KResult ::= Canonical

  // Programs are computations
  configuration <k> $PGM:Comp </k>

  // Beta rule for split (\beta.\times)
  rule [split]: split (V1,V2) with X1, X2 -> M => M[V1 / X1][V2 / X2]

  // Beta rules for case (\beta.+)
  rule [casel]: case inl(V) of { X1 -> M1 ; _  -> _  } => M1[V / X1]
  rule [caser]: case inr(V) of { _  -> _  ; X2 -> M2 } => M2[V / X2]

  // Beta rules for suspension and forcing (\beta.U)
  rule [force]: thunk(M:Comp)! => M

  // Beta rule for let (\beta.F)
  rule [let]: let X = return(V) in M => M[V / X]
  // Operation hosting rule for let, an instance of (hoist.op)
  rule [letOp]: let Y = [OP](V, \X -> M) in N => [OP](V, \X -> let Y = M in N)

  // Beta rule for application (\beta.->)
  rule [apply]: (lam X -> M) V => M[V / X]
  // Operation hosting rule for application, an instance of (hoist.op)
  rule [applyOp]: [OP](V, \X -> M) W => [OP](V, \X -> M W)

  // Beta rules for projection (\beta.&)
  rule [fst]: fst(< M, _ >) => M
  rule [snd]: snd(< _, M >) => M
  // Operation hosting rules for projection, an instance of (hoist.op)
  rule [fstOp]: fst([OP](V, \X -> M)) => [OP](V, \X -> fst(M))
  rule [sndOp]: snd([OP](V, \X -> M)) => [OP](V, \X -> snd(M))

  // Handling rule for values (handle.F)
  rule [handleVal]: handle return(V) with {return(X) -> M; _:HandlerOps}
                      => M[V / X]
  // Handling rule for operations (handle.op)
  //
  // We use the auxilliary function getOp to find the required operation in the
  // handler body, and then take the result and apply the rule.
  rule [handleOp]: (handle [OP](V, \X -> M) with {RET; OPS}):Comp
    => #fun(match(P, K, N)
              => N[V / P][thunk(lam X -> handle M with {RET; OPS}) / K]
           )(getOp(OP, OPS))

  // Successful result of getOp
  syntax OpMatch ::= match(KVar, KVar, Comp)
  // getOp
  syntax OpMatch ::= getOp(Id, HandlerOps) [function]
                   | "getOpFailure"
  // If the required op matches the first case, return the match
  rule getOp(OP1:Id, [OP2](X, K) -> M ; _:HandlerOps) => match(X, K, M)
       requires OP1 ==K OP2
  // Otherwise recurse
  rule getOp(OP1:Id, [OP2](_, _) -> _ ; OPS:HandlerOps) => getOp(OP1, OPS)
       requires OP1 =/=K OP2
  // And fail when we run out of options
  rule getOp(_:Id, .HandlerOps) => getOpFailure
endmodule