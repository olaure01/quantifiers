Require Import PeanoNat.
Require Import Wf_nat.
Require Import Lia.
Require Import List.
Require Import Equalities.

Ltac autorewrite_all := autorewrite with core in *.
Tactic Notation "rnow" tactic(t) := now t ; autorewrite_all.

(** * Different kinds of atoms *)

Parameter atom : Set. (* second-order constants *)
Parameter vatom : Set. (* variables for quantification *)
Parameter beq_vat : vatom -> vatom -> bool. (* boolean equality on [vatom] *)
Parameter beq_eq_vat : forall a b, beq_vat a b = true <-> a = b.
   (* equality specification for [vatom] *)

(* [vatom] presented as a type with Boolean equality *)
Module vatomBoolEq <: UsualBoolEq.
Definition t := vatom.
Definition eq := @eq vatom.
Definition eqb := beq_vat.
Definition eqb_eq := beq_eq_vat.
End vatomBoolEq.
Module vatomEq := Make_UDTF vatomBoolEq.
Module vatomFacts := BoolEqualityFacts vatomEq.
Import vatomFacts.

Lemma in_rmv : forall X Y, beq_vat Y X = false -> forall l,
  In X l -> In X (remove vatomEq.eq_dec Y l).
Proof.
induction l ; auto ; intros Hi.
inversion Hi ; subst ; simpl.
- destruct (vatomEq.eq_dec Y X) ; intuition.
  subst ; rewrite eqb_refl in H ; inversion H.
- destruct (vatomEq.eq_dec Y a) ; intuition.
Qed.

Hint Resolve in_rmv.




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

Lemma fsize_fup : forall k A, fsize (fup k A) = fsize A.
Proof.
induction A ; simpl ; intuition.
case_eq (n <? k) ; auto.
Qed.

Hint Rewrite fsize_fup.

Lemma fup_fup_com : forall k A,
  fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof.
induction A ; simpl ; f_equal ; intuition.
change (S n <? S k) with (n <? k) ; case_eq (n <? k) ; auto.
Qed.

Hint Rewrite fup_fup_com.



(** substitutes [formula] [F] for variable [X] in [formula] [A] (capture is possible) *)
Fixpoint subs X F A :=
match A with
| dvar k => dvar k
| var Y => if (beq_vat Y X) then F else var Y
| cst R => cst R
| top => top
| wdg B C => wdg (subs X F B) (subs X F C)
| frl Y B as C => if (beq_vat Y X) then C else frl Y (subs X F B)
end.

Lemma fsize_subs_dvar : forall k X A, fsize (subs X (dvar k) A) = fsize A.
Proof.
induction A ; simpl ; intuition ;
  case_eq (beq_vat v X) ; simpl ; auto.
Qed.

Hint Rewrite fsize_subs_dvar.


Lemma fup_subs_com : forall k X F A,
  fup k (subs X F A) = subs X (fup k F) (fup k A).
Proof.
intros ; induction A ; simpl ; f_equal ; intuition.
- now case_eq (beq_vat v X).
- now case_eq (n <? k).
- now case_eq (beq_vat v X) ; intuition ; simpl ; f_equal.
Qed.

Hint Rewrite fup_subs_com.




(** substitutes [formula] [F] for index [n] in [formula] [A] and decreases indexes above [n] *)
Fixpoint nsubs n F G :=
match G with
| var X => var X
| dvar k => match n ?= k with
            | Eq => F
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| cst R => cst R
| top => top
| wdg G1 G2 => wdg (nsubs n F G1) (nsubs n F G2)
| frl X G1 => frl X (nsubs n F G1)
end.

Lemma nsubs_fup_com : forall k F A,
  nsubs (S k) (fup 0 F) (fup 0 A) = fup 0 (nsubs k F A).
Proof.
intros ; induction A ; simpl ; f_equal ; intuition.
case_eq (k ?= n) ; auto.
intros Heq ; destruct n ; auto.
now destruct k.
Qed.

Hint Rewrite nsubs_fup_com.


Fixpoint freevars A :=
match A with
| var X => X :: nil
| dvar _ => nil
| cst _ => nil
| top => nil
| wdg B C => (freevars B) ++ (freevars C)
| frl X B => remove vatomEq.eq_dec X (freevars B)
end.

Lemma freevars_fup : forall k F, freevars (fup k F) = freevars F.
Proof.
induction F ; simpl ; f_equal ; intuition.
now case_eq (n <? k).
Qed.

Hint Rewrite freevars_fup.

Lemma freevars_nsubs : forall n F, freevars F = nil -> forall A,
  freevars (nsubs n F A) = freevars A.
Proof.
induction A ; simpl ; f_equal ; intuition.
now case_eq (n ?= n0).
Qed.

Hint Rewrite freevars_nsubs using assumption.

Lemma nfree_subs : forall X F A, ~ In X (freevars A) -> subs X F A = A.
Proof.
induction A ; simpl ; intuition ; f_equal ; intuition ;
  case_eq (beq_vat v X) ; intuition.
- now apply vatomEq.eqb_eq in H.
- now f_equal.
Qed.

Hint Rewrite nfree_subs using assumption.

Lemma subs_closed : forall X F A, freevars A = nil -> subs X F A = A.
Proof.
intros.
assert (~ In X (freevars A))
  by (intros Hf ; rewrite H in Hf ; inversion Hf).
rnow idtac.
Qed.

Hint Rewrite subs_closed using assumption.

Lemma nsubs_subs_com : forall X F n G, freevars G = nil -> forall A,
  nsubs n G (subs X F A) = subs X (nsubs n G F) (nsubs n G A).
Proof.
intros ; induction A ; simpl ; f_equal ; intuition ;
  try now (case_eq (beq_vat v X) ; intros ; simpl ; f_equal ; auto).
rnow case_eq (n ?= n0).
Qed.

Hint Rewrite nsubs_subs_com using assumption.

Lemma subs_z_nsubs_com : forall X n F, freevars F = nil -> forall A,
  nsubs (S n) F (subs X (dvar 0) A) = subs X (dvar 0) (nsubs (S n) F A).
Proof.
intros ; induction A ; simpl ; f_equal ; intuition ;
  try now (case_eq (beq_vat v X) ; intros ; simpl ; f_equal ; auto).
destruct n0 ; simpl ; auto.
rnow case_eq (n ?= n0).
Qed.

Hint Rewrite subs_z_nsubs_com using assumption.

Lemma nsubs_z_fup : forall F A, nsubs 0 F (fup 0 A) = A.
Proof.
now induction A ; simpl ; f_equal.
Qed.

Hint Rewrite nsubs_z_fup.

Lemma nsubs_z_subs_fup : forall F X A,
  nsubs 0 F (subs X (dvar 0) (fup 0 A)) = subs X F A.
Proof.
rnow induction A ; simpl ; f_equal ; auto ;
  case_eq (beq_vat v X) ; intros ; simpl ; f_equal.
Qed.

Hint Rewrite nsubs_z_subs_fup.






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
| frlr { X C A } : prove (fup 0 C) (subs X (dvar 0) (fup 0 A)) -> prove C (frl X A)
| frll { X A C } : forall F, freevars F = nil -> prove (subs X F A) C -> prove (frl X A) C.

Hint Constructors prove.

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
Theorem psubs k F (Hc : freevars F = nil) {C A} (pi : prove C A) :
  { pi' : prove (nsubs k F C) (nsubs k F A) | psize pi' = psize pi }.
Proof with autorewrite_all.
revert k F Hc ; induction pi ; intros k F' Hc ;
  try (destruct (IHpi k F' Hc) as [pi' Hs]) ;
  try (destruct (IHpi1 k F' Hc) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k F' Hc) as [pi2' Hs2]).
- exists (ax _) ; auto.
- exists (topr _) ; auto.
- exists (wdgr pi1' pi2') ; simpl ; auto.
- exists (wdgll _ pi') ; simpl ; auto.
- exists (wdglr _ pi') ; simpl ; auto.
- clear pi' Hs.
  rewrite <- (freevars_fup 0) in Hc.
  destruct (IHpi (S k) _ Hc) as [pi' Hs].
  simpl ; rewrite <- Hs ; clear Hs.
  revert pi'...
  intros pi' ; exists (frlr pi') ; reflexivity.
- simpl ; rewrite <- Hs ; clear Hs.
  revert pi'...
  rewrite <- (freevars_nsubs k F' Hc) in e.
  intros pi' ; exists (frll _ e pi') ; reflexivity.
Qed.

(** lift indexes above [k] in proof [pi] *)
Theorem pup k {C A} (pi : prove C A) :
  { pi' : prove (fup k C) (fup k A) | psize pi' = psize pi }.
Proof with autorewrite_all.
revert k ; induction pi ; intros k ;
  try (destruct (IHpi k) as [pi' Hs]) ;
  try (destruct (IHpi1 k) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k) as [pi2' Hs2]).
- exists (ax _) ; auto.
- exists (topr _) ; auto.
- exists (wdgr pi1' pi2') ; simpl ; auto.
- exists (wdgll _ pi') ; simpl ; auto.
- exists (wdglr _ pi') ; simpl ; auto.
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  simpl ; rewrite <- Hs ; clear Hs.
  revert pi'.
  change (dvar 0) with (fup (S k) (dvar 0))...
  intros pi' ; exists (frlr pi') ; reflexivity.
- simpl ; rewrite <- Hs ; clear Hs.
  revert pi'...
  rewrite <- (freevars_fup k) in e.
  intros pi' ; exists (frll _ e pi') ; reflexivity.
Qed.



(** * Cut Elimination *)

Theorem cutr : forall A B C (pi1 : prove A B) (pi2 : prove B C), prove A C.
Proof.
enough (forall n, forall A B C (pi1 : prove A B) (pi2 : prove B C),
          n = psize pi1 + psize pi2 -> prove A C)
  by (intros ; apply (H _ _ _ _ pi1 pi2 eq_refl)).
induction n using (well_founded_induction_type lt_wf) ; intros ; subst.
assert (IH : forall A B C (pi1' : prove A B) (pi2' : prove B C),
               psize pi1' + psize pi2' < psize pi1 + psize pi2 -> prove A C)
  by (intros ; eapply H ; eauto) ; clear H.
destruct pi2 ; intuition.
- apply wdgr.
  + apply (IH _ _ _ pi1 pi2_1) ; simpl ; lia.
  + apply (IH _ _ _ pi1 pi2_2) ; simpl ; lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
            (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                   psize pi1' + psize pi2' < psize pi1 + psize (wdgll B pi2) -> prove A1 C0),
         D = wdg A0 B -> prove A C)
    as IH2 by refine (IH2 _ _ _ _ _ _ _ IH eq_refl) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst ; intuition.
  + apply (IH _ _ _ pi1_1 pi2) ; simpl ; lia.
  + apply wdgll.
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
  + apply (frll F e).
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
            (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                psize pi1' + psize pi2' < psize pi1 + psize (wdglr B pi2) -> prove A1 C0),
         D = wdg B A0 -> prove A C)
    as IH2 by refine (IH2 _ _ _ _ _ _ _ IH eq_refl) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst ; intuition.
  + apply (IH _ _ _ pi1_2 pi2) ; simpl ; lia.
  + apply wdgll.
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
  + apply (frll F e).
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
- destruct (pup 0 pi1) as [pi1' Hs].
  apply frlr.
  apply (IH _ _ _ pi1' pi2) ; simpl ; lia.
- enough (forall A D (pi1 : prove A D) X A0 C F e (pi2 : prove (subs X F A0) C)
            (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                   psize pi1' + psize pi2' < psize pi1 + psize (frll F e pi2) -> prove A1 C0),
         D = frl X A0 -> prove A C)
    as IH2 by refine (IH2 _ _ _ _ _ _ _ _ _ IH eq_refl) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  + apply (frll F e) ; assumption.
  + apply wdgll.
    apply (IH _ _ _ pi1 (frll F e pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (frll F e pi2)) ; simpl ; lia.
  + destruct (psubs 0 F e pi1) as [pi1' Hs].
    simpl in IH ; rewrite <- Hs in IH ; clear Hs.
    revert pi1' IH ; autorewrite_all.
    intros pi1' IH ; apply (IH _ _ _ pi1' pi2) ; lia.
  + apply (frll F e).
    apply (IH _ _ _ pi1 (frll F0 e0 pi2)) ; simpl ; lia.
Qed.



(** * Hilbert style properties *)

Lemma frl_elim : forall A F X, freevars F = nil -> prove (frl X A) (subs X F A).
Proof.
intros A F X Hf.
now apply (frll F).
Qed.

Lemma frl_wdg : forall A B X, prove (frl X (wdg A B)) (wdg (frl X A) (frl X B)).
Proof.
intros A B X.
repeat constructor ; simpl ;
  now (apply (frll (dvar 0)) ; constructor).
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
enough (Hn : forall n A, fsize A = n -> prove A A)
  by (intros A ; refine (Hn _ _ eq_refl)).
induction n using (well_founded_induction_type lt_wf) ; intros ; subst.
destruct A.
- apply ax.
- apply ax.
- apply ax.
- apply topr.
- apply wdgr ; [ apply wdgll | apply wdglr ] ; refine (H _ _ _ eq_refl) ; simpl ; lia.
- apply frlr.
  simpl ; apply (frll (dvar 0) eq_refl).
  refine (H _ _ _ eq_refl) ; autorewrite_all ; simpl ; lia.
Qed.


