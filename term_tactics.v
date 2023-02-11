(* Some tactics for term manipulations *)

From Coq Require Import PeanoNat List.
From OLlibs Require Import dectype.

Create HintDb term_db.
Ltac Tauto.intuition_solver ::= auto with datatypes term_db.

Lemma ltb_S n m : (S n <? S m) = (n <? m).
Proof. reflexivity. Qed.
#[export] Hint Rewrite ltb_S : term_db.


Tactic Notation "rnow" tactic(t) :=
  t; try (now autorewrite with term_db in *); (* intuition may do too many intros *)
     simpl; autorewrite with term_db in *; cbn; intuition.
Tactic Notation "rnow" tactic(t) "then" tactic(t1) :=
  t; try (now autorewrite with term_db in *); (* intuition may do too many intros *)
     simpl; autorewrite with term_db in *; cbn; intuition t1; simpl; intuition.

Ltac rcauto := simpl; intuition; autorewrite with term_db in *; simpl; rnow (repeat case_analysis).
