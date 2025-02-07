(* Sequent Calculus for Second-Order Propositional Additive Linear Logic *)

From Stdlib Require Import PeanoNat Wf_nat Lia List.
From OLlibs Require Import dectype.
From Quantifiers Require Import term_tactics.

#[local] Hint Resolve in_in_remove : term_db.


Parameter atom : Type. (* second-order constants *)
Parameter vatom : DecType. (* variables for quantification *)


(** * Formulas *)

(** formulas *)
(** second-order formulas in the langage: true, conjunction, universal quantification *)
Inductive formula :=
| var : vatom -> formula
| dvar : nat -> formula
| cst : atom -> formula
| top : formula
| wdg : formula -> formula -> formula
| frl : vatom -> formula -> formula.

Ltac formula_induction A :=
  (try intros until A) ;
  let X := fresh "X" in
  let K := fresh "k" in
  let P := fresh "P" in
  let A1 := fresh A in
  let A2 := fresh A in
  let Y := fresh "X" in
  induction A as [ X | K | P | | A1 A2 | Y A ] ; simpl ; intros ;
    try (f_equal ; intuition) ; try ((rnow idtac) ; fail) ; try (rcauto ; fail).


(** size of formulas *)
Fixpoint fsize A :=
match A with
| var _ => 1
| dvar _ => 1
| cst _ => 1
| top => 1
| wdg B C => S (fsize B + fsize C)
| frl _ B => S (fsize B)
end.


(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X => var X
| dvar n => if n <? k then dvar n else dvar (S n)
| cst R => cst R
| top => top
| wdg B C => wdg (fup k B) (fup k C)
| frl X B => frl X (fup k B)
end.
Notation fupz := (fup 0).

Lemma fsize_fup : forall k A, fsize (fup k A) = fsize A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite fsize_fup : term_db.

Lemma fup_fup_com : forall k A,
  fup (S k) (fupz A) = fupz (fup k A).
Proof. formula_induction A. Qed.
#[local] Hint Rewrite fup_fup_com : term_db.


(** substitutes [formula] [F] for variable [X] in [formula] [A] (capture is possible) *)
Fixpoint subs X F A :=
match A with
| dvar k => dvar k
| var Y => if eq_dt_dec Y X then F else var Y
| cst R => cst R
| top => top
| wdg B C => wdg (subs X F B) (subs X F C)
| frl Y B => frl Y (if eq_dt_dec Y X then B else subs X F B)
end.

Lemma fsize_subs_dvar : forall k X A, fsize (subs X (dvar k) A) = fsize A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite fsize_subs_dvar : term_db.

Lemma fup_subs_com : forall k X F A,
  fup k (subs X F A) = subs X (fup k F) (fup k A).
Proof. now formula_induction A ; rcauto ; f_equal. Qed.
#[local] Hint Rewrite fup_subs_com : term_db.



(** substitutes [formula] [F] for index [n] in [formula] [A] and decreases indexes above [n] *)
Fixpoint nsubs n F A :=
match A with
| var X => var X
| dvar k => match n ?= k with
            | Eq => F
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| cst R => cst R
| top => top
| wdg B C => wdg (nsubs n F B) (nsubs n F C)
| frl X B => frl X (nsubs n F B)
end.

Lemma nsubs_fup_com : forall k F A,
  nsubs (S k) (fupz F) (fupz A) = fupz (nsubs k F A).
Proof. formula_induction A ; rcauto.
now destruct k0; destruct k; inversion Heq.
Qed.
#[local] Hint Rewrite nsubs_fup_com : term_db.


Fixpoint freevars A :=
match A with
| var X => X :: nil
| dvar _ => nil
| cst _ => nil
| top => nil
| wdg B C => (freevars B) ++ (freevars C)
| frl X B => remove eq_dt_dec X (freevars B)
end.
Notation closed A := (freevars A = nil).

Lemma closed_nofreevars A X : closed A -> ~ In X (freevars A).
Proof. intros Hc Hin. rewrite Hc in Hin. destruct Hin. Qed.

Lemma freevars_fup k A : freevars (fup k A) = freevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite freevars_fup : term_db.

Lemma freevars_nsubs n F (Hc : closed F) A : freevars (nsubs n F A) = freevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite freevars_nsubs using assumption : term_db.

Lemma nfree_subs X F A : ~ In X (freevars A) -> subs X F A = A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite nfree_subs using try tauto;
                                       try apply closed_nofreevars; tauto : term_db.

Lemma nsubs_subs_com X F n G (Hin : ~ In X (freevars G)) A :
  nsubs n G (subs X F A) = subs X (nsubs n G F) (nsubs n G A).
Proof. formula_induction A. Qed.
#[local] Hint Rewrite nsubs_subs_com using try tauto;
                                           try apply closed_nofreevars; tauto : term_db.

Lemma nsubs_z_fup F A : nsubs 0 F (fupz A) = A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite nsubs_z_fup : term_db.



(** * Proofs *)

(** Proofs *)
(** two-sided sequent calculus for second-order (additive) linear logic with connectives: 
    top, with, forall *)
Inductive prove : formula -> formula -> Type :=
| ax : forall A, prove A A
| topr : forall C, prove C top
| wdgr { C A B } : prove C A -> prove C B -> prove C (wdg A B)
| wdgll { A C } : forall B, prove A C -> prove (wdg A B) C
| wdglr { A C } : forall B, prove A C -> prove (wdg B A) C
| frlr { X C A } : prove (fupz C) (subs X (dvar 0) (fupz A)) -> prove C (frl X A)
| frll { X A C } : forall F, closed F -> prove (subs X F A) C -> prove (frl X A) C.
#[local] Hint Constructors prove : term_db.

(** height of proofs *)
Fixpoint psize {A B} (pi : prove A B) :=
match pi with
| ax _ => 1
| topr _ => 1
| wdgr pi1 pi2 => S (max (psize pi1) (psize pi2))
| wdgll _ pi1 => S (psize pi1)
| wdglr _ pi1 => S (psize pi1)
| frlr pi1 => S (psize pi1)
| frll _ _ pi1 => S (psize pi1)
end.

(** substitutes [cterm] [u] for index [n] in proof [pi] and decreases indexes above [n] *)
Theorem psubs k F (Hc : closed F) {C A} (pi : prove C A) :
  { pi' : prove (nsubs k F C) (nsubs k F A) | psize pi' = psize pi }.
Proof.
revert k F Hc; induction pi; intros k F' Hc;
  try (destruct (IHpi k F' Hc) as [pi' Hs]);
  try (destruct (IHpi1 k F' Hc) as [pi1' Hs1]);
  try (destruct (IHpi2 k F' Hc) as [pi2' Hs2]).
- now exists (ax _).
- now exists (topr _).
- exists (wdgr pi1' pi2'). cbn. auto.
- exists (wdgll _ pi'). cbn. auto.
- exists (wdglr _ pi'). cbn. auto.
- clear pi' Hs.
  rewrite <- (freevars_fup 0) in Hc.
  destruct (IHpi (S k) _ Hc) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  exists (frlr pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  rewrite <- (freevars_nsubs k F' Hc) in e.
  exists (frll _ e pi'). reflexivity.
Qed.

(** lift indexes above [k] in proof [pi] *)
Theorem pup k {C A} (pi : prove C A) : { pi' : prove (fup k C) (fup k A) | psize pi' = psize pi }.
Proof.
induction pi in k |- *;
  try (destruct (IHpi k) as [pi' Hs]) ;
  try (destruct (IHpi1 k) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k) as [pi2' Hs2]).
- now exists (ax _).
- now exists (topr _).
- exists (wdgr pi1' pi2'). cbn. auto.
- exists (wdgll _ pi'). cbn. auto.
- exists (wdglr _ pi'). cbn. auto.
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  cbn. rewrite <- Hs. clear Hs.
  revert pi'.
  rnow change (dvar 0) with (fup (S k) (dvar 0)).
  exists (frlr pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  rewrite <- (freevars_fup k) in e.
  exists (frll _ e pi'). reflexivity.
Qed.



(** * Cut Elimination *)

Theorem cutr A B C : prove A B -> prove B C -> prove A C.
Proof.
enough (forall n, forall A B C (pi1 : prove A B) (pi2 : prove B C),
              n = psize pi1 + psize pi2 -> prove A C) as H
  by (intros pi1 pi2 ; apply (H _ _ _ _ pi1 pi2 eq_refl)). clear A B C.
induction n as [n IH0] using (well_founded_induction_type lt_wf) ; intros ; subst.
assert (forall A B C (pi1' : prove A B) (pi2' : prove B C),
               psize pi1' + psize pi2' < psize pi1 + psize pi2 -> prove A C) as IH
  by (intros; eapply IH0; eauto); clear IH0.
destruct pi2; intuition.
- apply wdgr.
  + apply (IH _ _ _ pi1 pi2_1). cbn. lia.
  + apply (IH _ _ _ pi1 pi2_2). cbn. lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
            (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                   psize pi1' + psize pi2' < psize pi1 + psize (wdgll B pi2) -> prove A1 C0),
         D = wdg A0 B -> prove A C)
    as IH2 by refine (IH2 _ _ _ _ _ _ _ IH eq_refl); clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst; intuition;
    try (constructor ; apply (IH _ _ _ pi1 (wdgll _ pi2)); cbn; lia).
  + apply (IH _ _ _ pi1_1 pi2). cbn. lia.
  + apply (frll F e).
    apply (IH _ _ _ pi1 (wdgll _ pi2)). cbn. lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
            (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                psize pi1' + psize pi2' < psize pi1 + psize (wdglr B pi2) -> prove A1 C0),
         D = wdg B A0 -> prove A C)
    as IH2 by refine (IH2 _ _ _ _ _ _ _ IH eq_refl) ; clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst; intuition;
    try (constructor; apply (IH _ _ _ pi1 (wdglr _ pi2)); cbn; lia).
  + apply (IH _ _ _ pi1_2 pi2). cbn. lia.
  + apply (frll F e).
    apply (IH _ _ _ pi1 (wdglr _ pi2)). cbn. lia.
- destruct (pup 0 pi1) as [pi1' Hs].
  apply frlr, (IH _ _ _ pi1' pi2). cbn. lia.
- enough (forall A D (pi1 : prove A D) X A0 C F e (pi2 : prove (subs X F A0) C)
            (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                   psize pi1' + psize pi2' < psize pi1 + psize (frll F e pi2) -> prove A1 C0),
         D = frl X A0 -> prove A C)
    as IH2 by refine (IH2 _ _ _ _ _ _ _ _ _ IH eq_refl); clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst;
    try (constructor ; apply (IH _ _ _ pi1 (frll _ e pi2)); cbn; lia).
  + apply (frll F e). assumption.
  + destruct (psubs 0 F e pi1) as [pi1' Hs].
    simpl in IH. rewrite <- Hs in IH. clear Hs.
    revert pi1' IH. autorewrite with term_db. intros pi1' IH.
    apply (IH _ _ _ pi1' pi2). cbn. lia.
  + apply (frll F e), (IH _ _ _ pi1 (frll F0 e0 pi2)). cbn. lia.
Qed.



(** * Hilbert style properties *)

Lemma frl_elim : forall A F X, closed F -> prove (frl X A) (subs X F A).
Proof.
intros A F X Hc.
rnow apply (frll F).
Qed.

Lemma frl_wdg : forall A B X, prove (frl X (wdg A B)) (wdg (frl X A) (frl X B)).
Proof.
intros A B X.
repeat constructor; simpl;
  apply (frll (dvar 0)); simpl; do 2 constructor.
Qed.

Lemma frl_nfree : forall A X, ~ In X (freevars A) -> prove A (frl X A).
Proof.
intros A X Hnf.
rewrite <- (freevars_fup 0) in Hnf.
rnow apply frlr.
Qed.


(** * Other properties *)

(** Axiom expansion *)
Lemma ax_exp : forall A, prove A A.
Proof.
enough (Hn : forall n A, fsize A = n -> prove A A) by (intros A; refine (Hn _ _ eq_refl)).
induction n as [n IH] using (well_founded_induction_type lt_wf); intros; subst.
destruct A.
- apply ax.
- apply ax.
- apply ax.
- apply topr.
- apply wdgr; [ apply wdgll | apply wdglr ]; refine (IH _ _ _ eq_refl); cbn; lia.
- apply frlr.
  cbn. apply (frll (dvar 0) eq_refl). constructor.
Qed.
