Require Export SepAlg.

  Module Type LabeledSeqCalculus
    (Export sepalg : SepAlg).
    Local Open Scope sepscope.

    Inductive Exp :=
    | EVar (a : T)
    | EUnit
    | EAdd (a b : Exp).

    Variant Label := LVar (p : T) | LUnit.

    Variant TernaryRelAtom : Set :=  TRA : Label ->  Label -> Label -> TernaryRelAtom.
    Notation " a ; b ▻ c " := (TRA a b c) (at level 70, no associativity).

    Definition denoteLabel (l : Label) :=
      match l with
      | LVar p => p
      | LUnit => unit_op
      end.

    Fixpoint denoteExp (t : Exp) : T :=
      match t with
      | EVar i => i
      | EUnit => unit_op
      | EAdd a b => denoteExp a \+ denoteExp b
      end.

    Definition denoteTernaryRelAtom (t : TernaryRelAtom) : Prop :=
      match t with
      |  a ; b ▻ c  => denoteLabel a \+ denoteLabel b = denoteLabel c  /\ valid_op (denoteLabel c)
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

    Inductive Deriv :
      list TernaryRelAtom -> list (Label * Assertion) -> list (Label * Assertion) -> Prop :=
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

    | DAndL Ψ Γ Δ w A B :
      Ψ ;; (w , A) :: (w , B) :: Γ ⊢ Δ ->
      (* ---------------------------- *)
      Ψ ;; (w , AAnd A B ) :: Γ ⊢ Δ

    | DAndR Ψ Γ Δ w A B :
      Ψ ;; Γ ⊢ (w , A) :: Δ ->
      Ψ ;; Γ ⊢ (w , B) :: Δ ->
      (* ---------------------------- *)
      Ψ ;; Γ ⊢ (w , AAnd A B ) :: Δ

    | DImpL Ψ Γ Δ w A B :
      Ψ ;; Γ ⊢ (w, A) :: Δ ->
      Ψ ;; (w, B) :: Γ ⊢ Δ ->
      (* ------------------------- *)
      Ψ ;; (w , AImp A B) :: Γ ⊢ Δ

    | DImpR Ψ Γ Δ w A B :
      Ψ ;; (w, A) :: Γ ⊢ (w, B) :: Δ ->
      (* ------------------------- *)
      Ψ ;; Γ ⊢ (w , AImp A B) :: Δ

    | DStarL Ψ Γ Δ x y z A B :
      (x ; y ▻ z) ::
        Ψ ;;
      (x , A) :: (y , B) :: Γ
        ⊢ Δ ->
      (* ------------------------------ *)
      Ψ ;; (z, AStar A B) :: Γ ⊢ Δ

    | DWandR x y z Ψ Γ A B Δ :
      (x ; z ▻ y) :: Ψ ;; (x, A)::Γ ⊢ (y, B) :: Δ ->
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

    (* ---------- Structural rules ---------------------- *)
    | DE x y z Ψ Γ Δ :
      (y ; x ▻ z) :: (x ; y ▻ z) :: Ψ ;; Γ  ⊢ Δ ->
      (* ---------------------------------------- *)
      (x ; y ▻ z) :: Ψ ;; Γ ⊢ Δ

    | DA u w y v x z Ψ Γ Δ :
      (u ; w ▻ z) :: (y ; v ▻ w) :: (x ; y ▻ z) :: (u ; v ▻ x) :: Ψ ;; Γ ⊢ Δ ->
      (x ; y ▻ z) :: (u ; v ▻ x) :: Ψ ;; Γ ⊢ Δ


    where "Ψ ;; Γ ⊢ Δ" := (Deriv Ψ Γ Δ).

    Fixpoint denoteTernaries Ψ:=
      match Ψ with
      | nil => True
      | T::Ψ => denoteTernaryRelAtom T /\ denoteTernaries Ψ
      end.

    Fixpoint denoteSequentL Γ :=
      match Γ with
      | nil => True
      | (x , A)::Γ => denoteAssertion A (denoteLabel x) /\ denoteSequentL Γ
      end.

    Fixpoint denoteSequentR Δ :=
      match Δ with
      | nil => False
      | (x , A)::Δ => denoteAssertion A (denoteLabel x) \/ denoteSequentR Δ
      end.

    Definition SemDeriv Ψ Γ Δ : Prop :=
      denoteTernaries Ψ /\ denoteSequentL Γ -> denoteSequentR Δ.

    Notation "Ψ ;, Γ ⊨ Δ" := (SemDeriv Ψ Γ Δ) (at level 70, no associativity).

    Lemma DId_sound Ψ w p Γ Δ :
    (* ------------------- *)
      Ψ ;, (w , AVar p)::Γ ⊨ (w , AVar p)::Δ.
    Proof.
      move => //=. tauto.
    Qed.

    Lemma DEmpL_sound w (Ψ : list (TernaryRelAtom)) Γ Δ :
      IsZero w :: Ψ ;, Γ ⊨ Δ ->
      (* ------------------------- *)
      Ψ ;, (w , AEmp)::Γ ⊨ Δ.
    Proof.
      rewrite /SemDeriv => //= h [h0[h1 h2]].
      apply h => {h}.
      repeat split => //.
      - rewrite h1. by rewrite left_id.
      - apply valid_unit.
    Qed.

    (* DCut is admissible, but it's nice to include it *)
    Lemma DCut_sound Ψ Ψ' Γ Δ Γ' Δ' x A :
      Ψ ;, Γ ⊨ (x, A) :: Δ ->
      Ψ' ;, (x, A) :: Γ' ⊨ Δ' ->
    (* --------------------------- *)
      Ψ ++ Ψ' ;, Γ ++ Γ' ⊨ Δ ++ Δ'.
    Proof.
      rewrite /SemDeriv => //= h1 h2.
      (* Need to show that denote respects append *)
    Admitted.

    Lemma DBotL_sound Ψ Γ Δ w :
    (* -------------------------- *)
      Ψ ;, (w , ABot)::Γ ⊨ Δ.
    Proof.
      rewrite /SemDeriv => //=. tauto.
    Qed.

    Theorem soundness Ψ Γ Δ :
      Ψ ;; Γ ⊢ Δ  ->  Ψ ;, Γ ⊨ Δ.
    Proof.
      move => h.
      (* Same as induction h *)
      elim : Ψ Γ Δ / h.
      - auto using DId_sound.
      - eauto using DCut_sound.
      - auto using DBotL_sound.
      - auto using DEmpL_sound.
     (* ... *)
    Admitted.

    End LabeledSeqCalculus.
