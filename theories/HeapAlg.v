Require Import SepAlg.
From Coq Require Import FunctionalExtensionality.

Lemma some_eq_iff{T}: forall (a b: T),
    Some a = Some b <-> a = b.
Proof.
  split; intros.
  - inv H; reflexivity.
  - subst; reflexivity.
Qed.

Module HeapAlg <: SepAlg.
  
  Definition T := option (bool -> option nat).
  Definition unit_op := Some (fun _: bool => @None nat).

  Definition valid_op : T -> bool := 
    fun t => match t with
          | None => false
          | Some _ => true
          end.

  Definition join_op: T -> T -> T :=
    fun a b => match a, b with
            | Some f, Some g =>
                match f true, g true, f false, g false with
                | Some _, None, None, None => Some f
                | None, Some _, None, None => Some g
                | None, None, Some _, None => Some f
                | None, None, None, Some _ => Some g
                | Some _, None, Some _, None => Some f
                | None, Some _, None, Some _ => Some g
                | Some x, None, None, Some y => Some (fun c: bool => if c then Some x else Some y)
                | None, Some x, Some y, None => Some (fun c: bool => if c then Some x else Some y)
                | None, None, None, None => Some (fun _ => None)
                | _, _, _, _ => None
                end
            | None, _ => None
            | _, None => None
            end.

  (* WTF Why can't I do [Local Open Scope sepscope] *)
  Notation "n \+ m" := (join_op n m) (at level 50, left associativity).
  Lemma comm : forall a b, a \+ b = b \+ a.
  Proof.
    intros [f|] [g|]; cbn; auto.
    destruct (f true), (g true), (f false), (g false); auto.
  Qed.

  Lemma left_id: forall a, join_op a unit_op = a.
  Proof.
    unfold join_op, unit_op; destruct a; auto;
    destruct (o true) eqn:Hot; auto;
      destruct (o false) eqn:Hof; auto; subst.
    apply some_eq_iff, functional_extensionality; destruct x.
    - now rewrite Hot.
    - now rewrite Hof.
  Qed.
  
  Lemma assoc : forall a b c, (a \+ b) \+ c = a \+ (b \+ c).
  Proof.
    intros [f|] [g|] [h|]; cbn; auto;
      destruct (f true) eqn: Hft; auto;
      destruct (g true) eqn:Hgt; auto;
      destruct (f false) eqn:Hff; auto;
      destruct (g false) eqn:Hgf; auto;
      destruct (h true) eqn:Hht; auto;
      destruct (h false) eqn:Hhf; auto;
      repeat (rewrite ?Hft ?Hgt ?Hht ?Hff ?Hgf ?Hhf; cbn; auto).
  Qed.

  Lemma valid_monoL : forall a b,
      valid_op (a \+ b) -> valid_op a.
  Proof.
    unfold valid_op, join_op; destruct a eqn:Ha; cbn; auto.
  Qed.
    
  Lemma valid_unit : valid_op unit_op.
  Proof.
    now unfold valid_op, unit_op.
  Qed.

  (* WTF Why can't I not do [Include SepAlgFacts HeapAlg] *)
  Lemma valid_monoR : forall a b, valid_op (b \+ a) -> valid_op a.
  Proof.
    now intros; rewrite comm in H; apply valid_monoL with b.
  Qed.

  Lemma right_id : forall a, unit_op \+ a = a.
  Proof.
    intros; rewrite comm; apply left_id.
  Qed.

End HeapAlg.
    
