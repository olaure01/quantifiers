Require Import Vector.
Require List.
Import EqNotations.

(* TODO Uniformize use of implicit arguments in stdlib Vector *)

(* TODO remove when integrated in Coq (8.14 ?) *)

Lemma length_to_list A n (v : t A n): length (to_list v) = n.
Proof. induction v; simpl; auto. Qed.

Lemma of_list_to_list_opp A n (v: t A n):
  rew length_to_list _ _ _ in of_list (to_list v) = v.
Proof.
induction v as [ | h n v IHv ].
- now apply case0 with (P := fun v => v = nil A).
- replace (length_to_list _ _ (cons _ h _ v)) with (f_equal S (length_to_list _ _ v))
    by apply (Eqdep_dec.UIP_dec PeanoNat.Nat.eq_dec).
  simpl; rewrite map_subst_map.
  f_equal.
  now etransitivity; [ | apply IHv].
Qed.

Lemma to_list_nil A : to_list (nil A) = List.nil.
Proof. reflexivity. Qed.

Lemma to_list_cons A h n (v : t A n):
  to_list (cons A h n v) = List.cons h (to_list v).
Proof. reflexivity. Qed.

Lemma to_list_hd A n (v : t A (S n)) d:
  hd v = List.hd d (to_list v).
Proof. now rewrite (eta v). Qed.

Lemma to_list_last A n (v : t A (S n)) d:
  last v = List.last (to_list v) d.
Proof.
apply rectS with (v:=v); auto.
intros a k u IH.
rewrite to_list_cons.
simpl List.last.
now rewrite <- IH, (eta u).
Qed.

Lemma to_list_const A (a : A) n:
  to_list (const a n) = List.repeat a n.
Proof.
induction n as [ | n IHn ]; auto.
now simpl; rewrite <- IHn.
Qed.

Lemma to_list_nth_order A n (v : t A n) p (H : p < n) d:
  nth_order v H = List.nth p (to_list v) d.
Proof.
revert n v H; induction p as [ | p IHp ]; intros n v H;
  (destruct n; [ inversion H | rewrite (eta v) ]); auto.
now rewrite <- nth_order_tl with (H:=Lt.lt_S_n _ _ H), IHp.
Qed.

Lemma to_list_tl A n (v : t A (S n)):
  to_list (tl v) = List.tl (to_list v).
Proof. now rewrite (eta v). Qed.

Lemma to_list_append A n m (v1 : t A n) (v2 : t A m):
  to_list (append v1 v2) = List.app (to_list v1) (to_list v2).
Proof.
induction v1; simpl; auto.
now rewrite to_list_cons; f_equal.
Qed.

Lemma to_list_rev_append_tail A n m (v1 : t A n) (v2 : t A m):
  to_list (rev_append_tail v1 v2) = List.rev_append (to_list v1) (to_list v2).
Proof. revert m v2; induction v1; intros m v2; [ auto | now simpl; rewrite IHv1 ]. Qed.

Lemma to_list_rev_append A n m (v1 : t A n) (v2 : t A m):
  to_list (rev_append v1 v2) = List.rev_append (to_list v1) (to_list v2).
Proof. unfold rev_append; rewrite (Plus.plus_tail_plus n m); apply to_list_rev_append_tail. Qed.

Lemma to_list_rev A n (v : t A n):
  to_list (rev v) = List.rev (to_list v).
Proof.
unfold rev; rewrite (plus_n_O n); unfold eq_rect_r; simpl.
now rewrite to_list_rev_append, List.rev_alt.
Qed.

Lemma to_list_map A B (f : A -> B) n (v : t A n) :
  to_list (map f v) = List.map f (to_list v).
Proof.
induction v; simpl; auto.
now cbn; f_equal.
Qed.

Lemma to_list_fold_left A B f (b : B) n (v : t A n):
  fold_left f b v = List.fold_left f (to_list v) b.
Proof. revert b; induction v; simpl; auto. Qed.

Lemma to_list_fold_right A B f (b : B) n (v : t A n):
  fold_right f v b = List.fold_right f b (to_list v).
Proof. revert b; induction v; simpl; intros b; f_equal; auto. Qed.

Lemma to_list_Forall A P n (v : t A n):
  Forall P v <-> List.Forall P (to_list v).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v) as l.
  revert n v Heql; induction HF; intros n v Heql;
    destruct v; inversion Heql; subst; constructor; auto.
Qed.

Lemma to_list_Exists A P n (v : t A n):
  Exists P v <-> List.Exists P (to_list v).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v) as l.
  revert n v Heql; induction HF; intros n v Heql;
    destruct v; inversion Heql; subst; now constructor; auto.
Qed.

Lemma to_list_In A a n (v : t A n):
  In a v <-> List.In a (to_list v).
Proof.
split.
- intros HIn; induction HIn; now constructor.
- induction v; intros HIn; inversion HIn; subst; constructor; auto.
Qed.

Lemma to_list_Forall2 A B P n (v1 : t A n) (v2 : t B n) :
  Forall2 P v1 v2 <-> List.Forall2 P (to_list v1) (to_list v2).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v1) as l1.
  remember (to_list v2) as l2.
  revert n v1 v2 Heql1 Heql2; induction HF; intros n v1 v2 Heql1 Heql2.
  + destruct v1; [ | inversion Heql1 ].
    apply (case0 (Forall2 P (nil A))); constructor.
  + destruct v1; inversion Heql1; subst.
    rewrite (eta v2) in Heql2; inversion Heql2; subst.
    rewrite (eta v2); constructor; auto.
Qed.
