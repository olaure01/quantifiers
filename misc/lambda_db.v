(* Lambda-Calculus with de Bruijn Indices *)

Require Import Bool PeanoNat Compare_dec Lia Relations RelationClasses.

Inductive term :=
| var : nat -> term
| lam : term -> term
| app : term -> term -> term.

Fixpoint freeness t :=
match t with
| var x => S x
| lam u => pred (freeness u)
| app u v => max (freeness u) (freeness v)
end.

Fixpoint bounded n t :=
match t with
| var x => x <? n
| lam u => bounded (S n) u
| app u v => andb (bounded n u) (bounded n v)
end.
Notation isclosed := (bounded 0).

Lemma bounded_le : forall t n m, n <= m ->
  bounded n t = true -> bounded m t = true.
Proof.
induction t ; intros k m Hle IH.
- simpl in IH ; apply Nat.ltb_lt in IH.
  apply Nat.ltb_lt ; lia.
- apply IHt with (S k) ; intuition.
- simpl in IH ; apply andb_true_iff in IH as [Hb1 Hb2].
  simpl ; apply andb_true_iff ; split.
  + apply IHt1 with k ; intuition.
  + apply IHt2 with k ; intuition.
Qed.

Lemma bounded_freeness : forall t n,
  bounded n t = true <-> freeness t <= n.
Proof with simpl ; intuition.
split ; revert n.
- induction t ; simpl ; intros m Hb.
  + apply Nat.ltb_lt...
  + apply IHt in Hb...
  + apply andb_true_iff in Hb as [Hb1 Hb2].
    apply Nat.max_lub...
- induction t ; intros m...
  + apply Nat.ltb_lt...
  + apply andb_true_iff ; split ; [ apply IHt1 | apply IHt2 ] ; lia.
Qed.

Fixpoint up k t :=
match t with
| var x => if x <? k then var x else var (S x)
| lam u => lam (up (S k) u)
| app u v => app (up k u) (up k v)
end.

Lemma freeness_up : forall t k, freeness (up k t) <= S (freeness t).
Proof.
induction t ; simpl ; intros k ; simpl ; intuition.
- destruct (n <? k) ; simpl ; intuition.
- specialize IHt with (S k) ; lia.
- specialize IHt1 with k ; specialize IHt2 with k ; lia.
Qed.

Lemma bounded_up : forall t n k,
  bounded n t = true -> bounded (S n) (up k t) = true.
Proof.
intros t n k Hb.
apply bounded_freeness in Hb ; apply bounded_freeness.
etransitivity ; [ eapply freeness_up | ] ; lia.
Qed.

Fixpoint subs x w t :=
match t with
| var y => match x ?= y with
           | Eq => w
           | Lt => var (pred y)
           | Gt => var y
           end
| lam u => lam (subs (S x) (up 0 w) u)
| app u v => app (subs x w u) (subs x w v)
end.

Inductive beta_red : relation term :=
| beta_red0 : forall u v, beta_red (app (lam u) v) (subs 0 v u)
| beta_lam : forall t1 t2, beta_red t1 t2 -> beta_red (lam t1) (lam t2)
| beta_app_l : forall t1 t2 u, beta_red t1 t2 -> beta_red (app t1 u) (app t2 u)
| beta_app_r : forall t1 t2 u, beta_red t1 t2 -> beta_red (app u t1) (app u t2).

Notation beta_redeq := (clos_refl _ beta_red).
Notation beta_reds := (clos_refl_trans _ beta_red).
Instance beta_redeq_refl : Reflexive beta_redeq.
Proof. intros x ; apply r_refl. Qed.
Instance beta_reds_preorder : PreOrder beta_reds.
Proof.
split.
- intros x ; now constructor.
- intros x y z ; now econstructor ; eassumption.
Qed.

Fixpoint beta_hd t :=
match t with
| var y => var y
| lam u => lam (beta_hd u)
| app (lam u) v => subs 0 v u
| app u v => app (beta_hd u) v
end.

Fixpoint beta_hd_n n t :=
match n with
| 0 => t
| S k => beta_hd_n k (beta_hd t)
end.

Lemma bounded_subs : forall t x w n, x <= n ->
  bounded (S n) t = true -> bounded n w = true ->
  bounded n (subs x w t) = true.
Proof.
induction t ; intros x w k Hle Hb1 Hb2 ; simpl ; intuition.
- assert (x ?= n = Lt -> 0 < n)
    by (intros Heq ; destruct n ; destruct x ; inversion Heq ; lia).
  assert (HGt := nat_compare_gt x n).
  destruct (x ?= n) ; intuition.
  + simpl in Hb1 ; apply Nat.ltb_lt in Hb1.
    apply Nat.ltb_lt ; lia.
  + simpl in Hb1 ; apply Nat.ltb_lt in Hb1.
    apply Nat.ltb_lt ; intuition.
- apply IHt ; intuition.
  apply bounded_up ; intuition.
- simpl in Hb1 ; apply andb_true_iff in Hb1 as [Hb1' Hb1''].
  apply andb_true_iff ; intuition.
Qed.

Lemma bounded_beta_hd : forall t n,
  bounded n t = true -> bounded n (beta_hd t) = true.
Proof.
induction t ; simpl ; intros k IH ; intuition.
destruct t1 ; simpl in IH ; simpl ; intuition.
- apply andb_true_iff in IH as [Hb1 Hb2].
  apply bounded_subs ; intuition.
- destruct t1_1 ; simpl in IH ; simpl ; intuition.
  + apply andb_true_iff in IH as [Hb1 Hb2].
    apply andb_true_iff ; intuition.
  + apply andb_true_iff in IH as [Hb1 Hb2].
    apply andb_true_iff ; intuition.
    apply IHt1 ; intuition.
Qed.

Lemma closed_beta_hd : forall t,
  isclosed t = true -> isclosed (beta_hd t) = true.
Proof.
intros t Hc.
exact (bounded_beta_hd t 0 Hc).
Qed.

Lemma beta_red_beta_hd : forall t, beta_redeq t (beta_hd t).
Proof with simpl ; intuition.
induction t...
- destruct IHt...
  apply r_step ; constructor...
- destruct t1...
  + apply r_step ; constructor.
  + inversion IHt1 ; subst...
    apply r_step ; constructor...
Qed.

Lemma beta_reds_beta_hd_n : forall n t, beta_reds t (beta_hd_n n t).
Proof.
induction n ; intros t ; simpl.
- reflexivity.
- etransitivity.
  + apply clos_r_clos_rt.
    apply beta_red_beta_hd.
  + apply IHn.
Qed.


(* Examples *)

Notation tid := (lam (var 0)).

Goal isclosed tid = true.
Proof. reflexivity. Qed.
Goal beta_hd (app tid tid) = tid.
Proof. reflexivity. Qed.

Notation pi1 := (lam (lam (var 1))).
Notation pi2 := (lam (lam (var 0))).

Goal beta_hd_n 2 (app (app pi2 pi1) tid) = tid.
Proof. reflexivity. Qed.
Goal beta_hd_n 2 (app (app pi1 pi1) tid) = pi1.
Proof. reflexivity. Qed.

Notation tapp := (lam (lam (app (var 1) (var 0)))).

Goal beta_hd_n 2 (app (app tapp (var 0)) (var 1)) = app (var 0) (var 1).
Proof. reflexivity. Qed.
Goal isclosed (var 0) = false.
Proof. reflexivity. Qed.
Goal isclosed (app (var 0) (var 1)) = false.
Proof. reflexivity. Qed.

Notation delta := (lam (app (var 0) (var 0))).

Goal beta_hd (app delta delta) = app delta delta.
Proof. reflexivity. Qed.

Goal beta_hd_n 3 (app delta tapp) = tapp.
Proof. reflexivity. Qed.

