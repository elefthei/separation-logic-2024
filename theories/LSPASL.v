Require Export SepAlg.
Require Import Lists.List.
Require Import Logic.Classical_Prop.

  Module Type LabeledSeqCalculus
    (Export sepalg : SepAlg).
    Local Open Scope sepscope.

    Inductive Exp :=
    | EVar (a : T)
    | EUnit
    | EAdd (a b : Exp).

    Variant Label := LVar (p : T) | LUnit.

    Variant TernaryRelAtom : Set :=
      TRA : Label ->  Label -> Label -> TernaryRelAtom.
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

    Definition stop (_ : T) := True.
    Definition sbot (_ : T) := False.
    Definition sand P Q (a : T) := P a /\ Q a.
    Definition sor P Q (a : T) := P a \/ Q a.
    Definition simp P Q (a : T) : Prop := P a -> Q a.
    Definition semp (a : T) := a = unit_op.
    Definition sstar P Q (c : T) : Prop := exists a b, valid_op (a \+ b) /\ a \+ b = c /\ P a /\ Q b.
    Definition swand P Q (c : T) : Prop := forall a, P a -> Q (a \+ c).

    Fixpoint denoteAssertion P : T -> Prop  :=
      match P with
      | AVar p => p
      | ATop => stop
      | ABot => sbot
      | AAnd P Q => sand (denoteAssertion P) (denoteAssertion Q)
      | AOr P Q => sor (denoteAssertion P) (denoteAssertion Q)
      | AImp P Q => simp (denoteAssertion P) (denoteAssertion Q)
      | AEmp => semp
      | AStar P Q => sstar (denoteAssertion P) (denoteAssertion Q)
      | AWand P Q => swand (denoteAssertion P) (denoteAssertion Q)
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

    Lemma denoteTernaries_app: forall A B,
        denoteTernaries (A ++ B) <-> denoteTernaries A /\ denoteTernaries B.
    Proof.
      intros A B.
      remember (A ++ B) as AB.
      generalize dependent B.
      generalize dependent A.
      induction AB; intros; symmetry in HeqAB.
      - apply app_eq_nil in HeqAB as (-> & ->); cbn; intuition.
      - apply app_eq_cons in HeqAB.
        destruct HeqAB as [(-> & ->) | (tsA & -> & ->)], a.
        + specialize (IHAB nil AB); cbn in *; intuition.
        + specialize (IHAB tsA B); cbn in *; intuition.
    Qed.

    Lemma denoteSequentL_app: forall A B,
        denoteSequentL (A ++ B) <-> denoteSequentL A /\ denoteSequentL B.
    Proof.
      intros A B.
      remember (A ++ B) as AB.
      generalize dependent B.
      generalize dependent A.
      induction AB; intros; symmetry in HeqAB.
      - apply app_eq_nil in HeqAB as (-> & ->); cbn; intuition.
      - apply app_eq_cons in HeqAB.
        destruct HeqAB as [(-> & ->) | (tsA & -> & ->)], a.
        + specialize (IHAB nil AB); cbn in *; intuition.
        + specialize (IHAB tsA B); cbn in *; intuition.
    Qed.

    Lemma denoteSequentR_app: forall A B,
        denoteSequentR (A ++ B) <-> denoteSequentR A \/ denoteSequentR B.
    Proof.
      intros A B.
      remember (A ++ B) as AB.
      generalize dependent B.
      generalize dependent A.
      induction AB; intros; symmetry in HeqAB.
      - apply app_eq_nil in HeqAB as (-> & ->); cbn; intuition.
      - apply app_eq_cons in HeqAB.
        destruct HeqAB as [(-> & ->) | (tsA & -> & ->)], a.
        + specialize (IHAB nil AB); cbn in *; intuition.
        + specialize (IHAB tsA B); cbn in *; intuition.
    Qed.

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

    Lemma DEmpL_complete w (Ψ : list (TernaryRelAtom)) Γ Δ :
      Ψ ;, (w , AEmp)::Γ ⊨ Δ ->
      IsZero w :: Ψ ;, Γ ⊨ Δ.
    Proof.
      rewrite /SemDeriv => //= h h1.
      apply h.
      repeat split; try tauto.
      rewrite comm left_id in h1.
      tauto.
    Qed.

    (* DCut is admissible, but it's nice to include it *)
    Lemma DCut_sound Ψ Ψ' Γ Δ Γ' Δ' x A :
      Ψ ;, Γ ⊨ (x, A) :: Δ ->
      Ψ' ;, (x, A) :: Γ' ⊨ Δ' ->
    (* --------------------------- *)
      Ψ ++ Ψ' ;, Γ ++ Γ' ⊨ Δ ++ Δ'.
    Proof.
      rewrite /SemDeriv => //= h1 h2.
      intros (? & ?); auto.
      apply denoteTernaries_app in H.
      apply denoteSequentR_app.
      apply denoteSequentL_app in H0.
      intuition.
    Qed.

    Lemma DBotL_sound Ψ Γ Δ w :
    (* -------------------------- *)
      Ψ ;, (w , ABot)::Γ ⊨ Δ.
    Proof.
      rewrite /SemDeriv //= /sbot . tauto.
    Qed.

    Lemma DTopR_sound  Ψ Γ w  Δ :
      Ψ ;, Γ ⊨ (w, ATop) :: Δ.
    Proof.
      rewrite /SemDeriv //= /stop. tauto.
    Qed.

    Lemma DEmpR_sound Ψ Γ Δ :
      Ψ ;, Γ ⊨ (LUnit, AEmp) :: Δ.
    Proof.
      rewrite /SemDeriv //= /semp. tauto.
    Qed.

    Lemma DAndL_sound Ψ Γ Δ w A B :
      Ψ ;, (w , A) :: (w , B) :: Γ ⊨ Δ ->
      (* ---------------------------- *)
      Ψ ;, (w , AAnd A B ) :: Γ ⊨ Δ.
    Proof.
      rewrite /SemDeriv //= /sand. tauto.
    Qed.

    Lemma DAndR_sound Ψ Γ Δ w A B :
      Ψ ;, Γ ⊨ (w , A) :: Δ ->
      Ψ ;, Γ ⊨ (w , B) :: Δ ->
      (* ---------------------------- *)
      Ψ ;, Γ ⊨ (w , AAnd A B ) :: Δ.
    Proof.
      rewrite /SemDeriv //= /sand. tauto.
    Qed.

    Lemma DImpL_sound Ψ Γ Δ w A B :
      Ψ ;, Γ ⊨ (w, A) :: Δ ->
      Ψ ;, (w, B) :: Γ ⊨ Δ ->
      (* ------------------------- *)
      Ψ ;, (w , AImp A B) :: Γ ⊨ Δ.
    Proof.
      rewrite /SemDeriv //= /simp. tauto.
    Qed.

    Lemma DImpR_sound Ψ Γ Δ w A B :
      Ψ ;, (w, A) :: Γ ⊨ (w, B) :: Δ ->
      (* ------------------------- *)
      Ψ ;, Γ ⊨ (w , AImp A B) :: Δ.
    Proof.
      rewrite /SemDeriv //= /simp /imply_to_or. tauto.
    Qed.

    Lemma DStarL_sound Ψ Γ Δ x y z A B :
      (x ; y ▻ z) ::
        Ψ ;,
      (x , A) :: (y , B) :: Γ
        ⊨ Δ ->
      (* ------------------------------ *)
      Ψ ;, (z, AStar A B) :: Γ ⊨ Δ.
    Proof.
      unfold SemDeriv. simpl. unfold sstar.
      intros ? (? & (a & b & ? & ? & ? & ?) & ?); subst.
      apply H; repeat split;
        rewrite <- ?H2; try tauto.
      - (* LEF: I don't think [join_cancelL] is enough to prove this,
         maybe something is missing. *)
        admit.
    Admitted.

    #[local]Hint Resolve DId_sound DCut_sound DBotL_sound DEmpL_sound DAndL_sound DAndR_sound DImpL_sound DImpR_sound DTopR_sound DEmpR_sound : sound.

    Theorem soundness Ψ Γ Δ :
      Ψ ;; Γ ⊢ Δ  ->  Ψ ;, Γ ⊨ Δ.
    Proof.
      move => h.
      (* Same as induction h *)
      elim : Ψ Γ Δ / h; eauto with sound.
    Admitted.

  End LabeledSeqCalculus.
