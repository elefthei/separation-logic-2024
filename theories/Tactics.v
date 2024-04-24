Require Import LSPASL.
From Ltac2 Require Ltac2.
Import Ltac2.

Module Solver
  (Export sepalg : SepAlg)
  (Export seqCalc : LabeledSeqCalculus sepalg).
  Ltac2 rec reify a :=
    lazy_match! a with
    | True => 'ATop
    | False => 'ABot
    | (fun a => a = unit_op) => 'AEmp
    | ?p /\ ?q =>
        let a := reify p in
        let b := reify q in
        '(AAnd $a $b)
    | ?p \/ ?q =>
        let a := reify p in
        let b := reify q in
        '(AOr $a $b)
    | ?p -> ?q =>
        let a := reify p in
        let b := reify q in
        '(AImp $a $b)
    | ?p
    | _ => Control.backtrack_tactic_failure "failed to reify"
    end.


End Solver.
