Require Export ssrbool ssreflect fintype.
From Hammer Require Export Tactics.

Ltac inv H := inversion H; subst; clear H.
