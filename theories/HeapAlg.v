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
            | None, a => None
            | a, None => None
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
  
  Lemma join_cancelL : forall a b c,
      valid_op (a \+ c) -> a \+ c = b \+ c -> a = b.
  Proof.
    (* Only consider [valid a, b, c] *)
    intros a b c Hac H.
    assert (Hbc: valid_op (b \+ c)) by now rewrite H in Hac.
    assert (Ha: valid_op a) by now apply valid_monoL in Hac.
    assert (Hb: valid_op b) by now apply valid_monoL in Hbc.
    assert (Hc: valid_op c) by now apply valid_monoR in Hac.
    destruct a as [a|]; destruct b as [b|]; destruct c as [c|];
      unfold valid_op in Ha, Hb, Hc;
      cbn in Ha, Hb, Hc;
      match goal with
      | [H: is_true false |- _ ] => inv H
      | _ => idtac
      end; clear Ha Hb Hc.
    (* Inversion of H *)
    apply some_eq_iff, functional_extensionality.
    unfold join_op in *.    
    intros [];
      destruct (a true) eqn: Hft; auto;
      destruct (a false) eqn:Hff; auto;
      destruct (b true) eqn:Hgt; auto;
      destruct (b false) eqn:Hgf; auto;
      destruct (c true) eqn:Hht; auto;
      destruct (c false) eqn:Hhf; auto;
      rewrite ?Hft ?Hgt ?Hht ?Hff ?Hgf ?Hhf in H;
      repeat (lazymatch goal with
              | [H: is_true (valid_op None) |- _ ] => inv H
              | [H: Some ?a = Some ?b |- _ ] => inv H
              | [H: None = Some ?b |- _ ] => inversion H
              | [H: Some ?a = None |- _ ] => inversion H
              | _ => fail
              end); rewrite <- ?Hft, <- ?Hgt, <- ?Hht, <- ?Hff, <- ?Hgf, <- ?Hhf; auto;
      rewrite ?Hff in Hgf; inv Hgf;
      rewrite ?Hft in Hgt; inv Hgt.
     - apply equal_f with true in H1; inv H1; now rewrite Hft.
     - apply equal_f with false in H1; inv H1; now rewrite Hff. 
  Qed.       

End HeapAlg.
    
