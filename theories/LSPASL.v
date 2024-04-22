From Hammer Require Import Hammer.
Require Export SepAlg.

Inductive Exp n :=
| EVar (i : fin n)
| EUnit
| EAdd (a b : Exp n).

Arguments EVar {n}.
Arguments EUnit {n}.
Arguments EAdd {n}.

  Module Type LabeledSeqCalculus
    (Export sepalg : SepAlg).
    Local Open Scope sepscope.


    Variant Label n := LVar (p : fin n) | LUnit.
    Arguments LVar{n}.
    Arguments LUnit{n}.

    Variant TernaryRelAtom n : Type :=  TRA : Label n ->  Label n -> Label n -> TernaryRelAtom n.
    Arguments TRA {n}.
    Notation " a ; b ▻ c " := (TRA a b c) (at level 70, no associativity).

    Definition denoteLabel {n} (ρ : fin n -> T) (l : Label n) :=
      match l with
      | LVar p => ρ p
      | LUnit => unit_op
      end.

    Fixpoint denoteExp {n} (ρ : fin n -> T) (t : Exp n) : T :=
      match t with
      | EVar i => ρ i
      | EUnit => unit_op
      | EAdd a b => denoteExp ρ a \+ denoteExp ρ b
      end.

    Definition denoteTernaryRelAtom {n} (ρ : fin n -> T) (t : TernaryRelAtom n) : Prop :=
      match t with
      |  a ; b ▻ c  => denoteLabel ρ a \+ denoteLabel ρ b = denoteLabel ρ c  /\ valid_op (denoteLabel ρ c)
      end.

    Notation IsZero a := (LUnit ; a ▻ LUnit).

    (* The Assertion variables are shallow-embedded, unlike the Exp variables *)
    Inductive Assertion : Type :=
    | AVar (p : T -> Prop)
    | ATop
    | ABot
    | AAnd (P Q : Assertion)
    | AOr (P Q : Assertion)
    | AImp (P Q : Assertion)
    (* Separation assertions *)
    | AEmp
    | AStar (P Q : Assertion)
    | AWand (P Q : Assertion).

    Fixpoint denoteAssertion P : T -> Prop  :=
      match P with
      | AVar p => p
      | ATop => fun _ => True
      | ABot => fun _ => False
      | AAnd P Q => fun a => denoteAssertion P a /\ denoteAssertion Q a
      | AOr P Q => fun a => denoteAssertion P a \/ denoteAssertion Q a
      | AImp P Q => fun a => denoteAssertion P a -> denoteAssertion Q a
      | AEmp => fun a => a = unit_op
      | AStar P Q => fun c => exists a b, valid_op (a \+ b) /\ a \+ b = c /\ denoteAssertion P a /\ denoteAssertion P b
      | AWand P Q => fun c => forall a, denoteAssertion P a -> denoteAssertion Q (a \+ c)
      end.

    Reserved Notation "Ψ ;; Γ ⊢ Δ" (at level 90 , no associativity).

    Definition shiftL {n} (l : Label n) : Label (S n).
      refine (match l with
      | LVar p => LVar _
      | LUnit => LUnit
              end).
      simpl.
      exact (Some p).
    Defined.

    Definition shiftHyps {n} (Γ : list (Label n * Assertion)) : list (Label (S n) * Assertion).
      revert Γ.
      apply map.
      intros (a & b).
      split.
      revert a. apply shiftL.
      exact b.
    Defined.

    Definition shiftATom {n} (t : TernaryRelAtom n) : TernaryRelAtom (S n) :=
      match t with
      | TRA a b c => TRA (shiftL a) (shiftL b) (shiftL c)
      end.

    Definition shiftTAtoms  {n} (Γ : list (TernaryRelAtom n)) :
      list (TernaryRelAtom (S n)).
      revert Γ.
      apply map.
      apply shiftATom.
    Defined.

    Inductive Deriv {n} :
      list (TernaryRelAtom n) -> list (Label n * Assertion) -> list (Label n * Assertion) -> Prop :=
    | DId Ψ w p Γ Δ :
    (* ------------------- *)
      Ψ ;; (w , AVar p)::Γ ⊢ (w , AVar p)::Δ

    | DCut Ψ Ψ' Γ Δ Γ' Δ' x A :
      Ψ ;; Γ ⊢ (x, A) :: Δ ->
      Ψ' ;; (x, A) :: Γ' ⊢ Δ' ->
    (* --------------------------- *)
      Ψ ++ Ψ' ;; Γ ++ Γ' ⊢ Δ ++ Δ'

    | DBotL Ψ Γ Δ w :
    (* -------------------------- *)
      Ψ ;; (w , ABot)::Γ ⊢ Δ

    | DEmpL w Ψ Γ Δ :
      IsZero w :: Ψ ;; Γ ⊢ Δ ->
      (* ------------------------- *)
      Ψ ;; (w , AEmp)::Γ ⊢ Δ

    | DTopR Ψ Γ w  Δ :
      Ψ ;; Γ ⊢ (w, ATop) :: Δ

    | DEmpR Ψ Γ Δ :
      Ψ ;; Γ ⊢ (LUnit, AEmp) :: Δ

    (* Some var_zero is just 1 + 0 *)
    (* After shifting the context by 2 through two consecutive uses of
    shiftHyps/shiftTAtoms, the numbers 0 and 1 become fresh
    variables *)
    | DStarL Ψ (Γ  : list (Label n * Assertion)) Δ z A B :
      (LVar var_zero ; LVar (Some var_zero : fin (S (S n))) ▻ shiftL (shiftL z)) ::
        (shiftTAtoms (shiftTAtoms Ψ)) ;;
      (LVar var_zero , A) :: (LVar (Some var_zero : fin (S (S n))) , B) :: (shiftHyps (shiftHyps Γ) )
        ⊢ (shiftHyps (shiftHyps Δ)) ->
      (* ------------------------------ *)
      Ψ ;; (z, AStar A B) :: Γ ⊢ Δ

    | DWandR z Ψ Γ A B Δ :
      (LVar var_zero ; shiftL (shiftL z) ▻ LVar (Some var_zero : fin (S (S n)))) :: (shiftTAtoms (shiftTAtoms Ψ)) ;; (LVar var_zero, A)::(shiftHyps (shiftHyps Γ)) ⊢ (LVar (Some var_zero : fin (S (S n))), B) :: (shiftHyps (shiftHyps Δ)) ->
      (* ----------------------------------- *)
      Ψ ;; Γ ⊢ (z, AWand A B) :: Δ

    | DStarR x y z Ψ Γ A B Δ :
      (x ; y ▻ z) :: Ψ ;; Γ ⊢ (x, A) :: (z , AStar A B) :: Δ ->
      (x ; y ▻ z) :: Ψ ;; Γ ⊢ (y, B) :: (z , AStar A B) :: Δ ->
      (* ---------------------------- *)
      (x ; y ▻ z) :: Ψ ;; Γ ⊢ (z,AStar A B) :: Δ

    | DWandL x y z Ψ Γ A B Δ :
      (x ; y ▻ z) :: Ψ ;; (y , AWand A B) :: Γ ⊢ (x, A)::Δ ->
      (x ; y ▻ z) :: Ψ ;; (y , AWand A B) :: (z , B) :: Γ ⊢ Δ ->
    (* --------------------- *)
      (x ; y ▻ z) :: Ψ ;; (y , AWand A B) :: Γ ⊢ Δ

    where "Ψ ;; Γ ⊢ Δ" := (Deriv Ψ Γ Δ).

    Fixpoint denoteTernaries {n} (ρ : fin n -> T) Ψ:=
      match Ψ with
      | nil => True
      | T::Ψ => denoteTernaryRelAtom ρ T /\ denoteTernaries ρ Ψ
      end.

    Fixpoint denoteSequentL {n} (ρ : fin n -> T) Γ :=
      match Γ with
      | nil => True
      | (x , A)::Γ => denoteAssertion A (denoteLabel ρ x) /\ denoteSequentL ρ Γ
      end.

    Fixpoint denoteSequentR {n} (ρ : fin n -> T) Δ :=
      match Δ with
      | nil => False
      | (x , A)::Δ => denoteAssertion A (denoteLabel ρ x) \/ denoteSequentR ρ Δ
      end.

    Definition SemDeriv {n} Ψ Γ Δ : Prop :=
      forall (ρ : fin n -> T), denoteTernaries ρ Ψ /\ denoteSequentL ρ Γ -> denoteSequentR ρ Δ.

    Notation "Ψ ;, Γ ⊨ Δ" := (SemDeriv Ψ Γ Δ) (at level 70, no associativity).

    Lemma DId_sound {n} (Ψ : list (TernaryRelAtom n)) w p Γ Δ :
    (* ------------------- *)
      Ψ ;, (w , AVar p)::Γ ⊨ (w , AVar p)::Δ.
    Proof.
      move => ρ //=. tauto.
    Qed.

    Lemma DEmpL_sound {n} w (Ψ : list (TernaryRelAtom n)) Γ Δ :
      IsZero w :: Ψ ;, Γ ⊨ Δ ->
      (* ------------------------- *)
      Ψ ;, (w , AEmp)::Γ ⊨ Δ.
    Proof.
      rewrite /SemDeriv => //= h ρ [h0[h1 h2]].
      apply h => {h}.
      repeat split => //.
      - rewrite h1. by rewrite left_id.
      - apply valid_unit.
    Qed.

    Theorem soundness {n} (Ψ : list (TernaryRelAtom n)) Γ Δ :
      Ψ ;; Γ ⊢ Δ  ->  Ψ ;, Γ ⊨ Δ.
    Admitted.

    End LabeledSeqCalculus.
