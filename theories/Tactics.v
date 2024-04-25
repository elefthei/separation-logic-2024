Require Import LSPASL.
From Ltac2 Require Ltac2.
Import Ltac2.

Module Solver
  (Export sepalg : SepAlg)
  (Export seqCalc : LabeledSeqCalculus sepalg).

  Definition elemIn (a : T) A : Prop := A a.
  Notation "a ∈ A" := (elemIn a A) (at level 70, no associativity).

  Ltac2 rec reify a :=
    lazy_match! a with
    | stop => 'ATop
    | sbot => 'ABot
    | semp => 'AEmp
    | sand ?p ?q =>
        let a := reify p in
        let b := reify q in
        '(AAnd $a $b)
    | sor ?p ?q =>
        let a := reify p in
        let b := reify q in
        '(AOr $a $b)
    | simp ?p ?q =>
        let a := reify p in
        let b := reify q in
        '(AImp $a $b)
    | sstar ?p ?q =>
        let a := reify p in
        let b := reify q in
        '(AStar $a $b)
    | swand ?p ?q =>
        let a := reify p in
        let b := reify q in
        '(AWand $a $b)
    | _ => Control.backtrack_tactic_failure "failed to reify"
    end.

End Solver.
