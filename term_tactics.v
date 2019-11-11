(* Some tactics for term manipulations *)

Require Import PeanoNat List.
Require Import dectype.

Create HintDb term_db.

Lemma ltb_S : forall n m, (S n <? S m) = (n <? m).
Proof. reflexivity. Qed.
Hint Rewrite ltb_S : term_db.

Tactic Notation "rnow" tactic(t) :=
  t; simpl; intuition; autorewrite with term_db in *; simpl; intuition.
Tactic Notation "rnow" tactic(t) "then" tactic(t1) :=
  t; simpl; intuition; autorewrite with term_db in *; simpl; intuition t1; simpl; intuition.

Ltac rcauto := simpl; autorewrite with term_db in *; simpl; rnow (repeat case_analysis).

Ltac in_solve :=
  simpl; repeat split;
  repeat (apply in_or_app; simpl);
  repeat match goal with
  | H : ?P /\ ?Q |- _ => destruct H
  end;
  repeat match goal with
  | H : In _ _ |- _ => simpl in H; apply in_app_or in H; destruct H
  end;
  intuition; fail.

