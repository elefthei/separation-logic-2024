Require Import LSPASL.
From Ltac2 Require Ltac2.
Require Import ssreflect.
Import Ltac2.

Set Default Proof Mode "Classic".
Module Solver
  (Export sepalg : SepAlg)
  (Export seqCalc : LabeledSeqCalculus sepalg).
  Module sfacts := SepAlgFacts sepalg.
  Import sfacts.

  Definition elemIn (a : T) A : Prop := A a.
  Notation "a ∈ A" := (elemIn a A) (at level 70, no associativity).

  Ltac2 rec reifyAssertion a :=
    match! a with
    | stop => 'ATop
    | sbot => 'ABot
    | semp => 'AEmp
    | sand ?p ?q =>
        let a := reifyAssertion p in
        let b := reifyAssertion q in
        '(AAnd $a $b)
    | sor ?p ?q =>
        let a := reifyAssertion p in
        let b := reifyAssertion q in
        '(AOr $a $b)
    | simp ?p ?q =>
        let a := reifyAssertion p in
        let b := reifyAssertion q in
        '(AImp $a $b)
    | sstar ?p ?q =>
        let a := reifyAssertion p in
        let b := reifyAssertion q in
        '(AStar $a $b)
    | swand ?p ?q =>
        let a := reifyAssertion p in
        let b := reifyAssertion q in
        '(AWand $a $b)
    | ?p =>'(AVar $p)
    | ?x => Control.backtrack_tactic_failure "failed to reify assertions"
    end.
  Local Open Scope sepscope.

  Ltac2 rec reifyExp a :=
    lazy_match! a with
    | ?a \+ ?b =>
        let e1 := reifyExp a in
        let e2 := reifyExp b in
        '(EAdd $e1 $e2)
    | unit_op => 'EUnit
    | _ => '(EVar $a)
    end.

  Fixpoint expToRelAtoms a : list TernaryRelAtom :=
    match a with
    | EAdd a b =>
        (denoteExp a ; denoteExp b ▻
        denoteExp a \+ denoteExp b) :: (expToRelAtoms a ++ expToRelAtoms b)
    | EUnit =>
        IsZero unit_op :: nil
    | EVar a =>
        nil
    end.

  Lemma expToRelAtoms_sound (a : Exp) :
    valid_op (denoteExp a) ->
    denoteTernaries (expToRelAtoms a).
  Proof.
    elim : a => //=.
    - rewrite left_id. tauto.
    - move => a iha b ihb /[dup] /[dup] ? /valid_monoL ? /valid_monoR ?.
      split => //.
      rewrite denoteTernaries_app.
      tauto.
  Qed.

  Lemma transform_sound (a : Exp) (A : Assertion) :
    valid_op (denoteExp a) ->
    expToRelAtoms a ;; nil ⊢ ((denoteExp a , A) :: nil) ->
    denoteExp a ∈ denoteAssertion A.
  Proof.
    move => + /soundness.
    rewrite /SemDeriv //=.
    have := expToRelAtoms_sound a.
    tauto.
  Qed.

  Ltac2 reifyGoal () :=
    lazy_match! goal with
    | [|- ?a ∈ ?p] =>
        let ar := reifyExp a in
        let pr := reifyAssertion p in
        apply (transform_sound $ar $pr)
    | [|- _] => Control.backtrack_tactic_failure "failed to reify the goal"
    end.

  Lemma ex1 : unit_op ∈ semp.
  Proof.
    ltac2:(reifyGoal ()); first by apply valid_unit.
    eauto.
  Qed.

  Lemma ex2 : unit_op \+ unit_op ∈ sstar semp semp.
  Proof.
    ltac2:(reifyGoal ()); simpl.
    - rewrite left_id. exact valid_unit.
    - eauto.
  Qed.

  Lemma ex3 (a b : T) (A B : T -> Prop) :
    valid_op (a \+ b) ->
    a \+ b ∈ simp (sstar A B) (sstar B A).
  Proof.
    move => h.
    ltac2:(reifyGoal ()) => //=.
    apply DImpR.
    apply DStarL => x y.
    apply DE.
    apply DStarR; auto.
    eapply DPerm with (Γ' := (y, AVar B) :: (x, AVar A) :: nil);
        solve [reflexivity | sfirstorder].
  Qed.

End Solver.
