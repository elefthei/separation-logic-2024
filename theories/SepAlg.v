Require Export common.

(** Cancellative separation algebra  *)
Module Type SepAlg.
Declare Scope sepscope.
Local Open Scope sepscope.
(** Carrier set *)
Parameter T : Set.

Parameter valid_op : T -> bool.

Parameter join_op : T -> T -> T.
Notation "n \+ m" := (join_op n m) (at level 50, left associativity) : sepscope.

Parameter unit_op : T.

Parameter comm : forall a b, a \+ b = b \+ a.

Parameter assoc : forall a b c, (a \+ b) \+ c = a \+ (b \+ c).

Parameter left_id : forall a, a \+ unit_op = a.

Parameter valid_monoL : forall a b,
    valid_op (a \+ b) -> valid_op a.

Parameter valid_unit : valid_op unit_op.

Parameter join_cancelL : forall a b c,
    valid_op (a \+ c) -> a \+ c = b \+ c -> a = b.

End SepAlg.

Module SepAlgFacts (Import M : SepAlg).
  Open Scope sepscope.

  Lemma valid_monoR : forall a b, valid_op (b \+ a) -> valid_op a.
  Proof.
    move => a b. rewrite comm. apply valid_monoL.
  Qed.

  Lemma right_id : forall a, unit_op \+ a = a.
  Proof.
    move => a. rewrite comm. apply left_id.
  Qed.

End SepAlgFacts.
