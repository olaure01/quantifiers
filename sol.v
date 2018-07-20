(* Coq 8.7.1 *)

Require Import PeanoNat.
Require Import EqNat.
Require Import Omega.
Require Import Lia.
Require Import List.
Require Import Equalities.


(** * Preliminaries *)

Lemma notltb_le : forall n k, (n <? k) = false <-> k <= n.
Proof.
intros n k ; case_eq (n <? k) ; intros Heq ; split.
- intros H ; inversion H.
- intros H ; apply Nat.ltb_lt in Heq ; omega.
- unfold Nat.ltb in Heq.
  intros.
  revert k Heq ; clear ; induction n ; intros k Heq.
  + destruct k ; try omega.
    inversion Heq.
  + destruct k ; try omega.
    apply le_n_S.
    apply IHn.
    apply Heq.
- intros ; reflexivity.
Qed.

(** Automatic solving for properties on [nat] written with Boolean predicates *)
Ltac boolnat_omega :=
repeat
  (match goal with
   | H : Nat.compare _ _ = Eq  |- _ => apply Nat.compare_eq_iff in H
   | H : Nat.compare _ _ = Lt  |- _ => apply Nat.compare_lt_iff in H
   | H : Nat.compare _ _ = Gt  |- _ => apply Nat.compare_gt_iff in H
   | H : Nat.eqb _ _ = true  |- _ => apply Nat.eqb_eq in H
   | H : Nat.ltb _ _ = true  |- _ => apply Nat.ltb_lt in H
   | H : Nat.leb _ _ = true  |- _ => apply Nat.leb_le in H
   | H : Nat.ltb _ _ = false  |- _ => apply notltb_le in H
   | |- Nat.compare _ _ = Eq => apply Nat.compare_eq_iff
   | |- Nat.compare _ _ = Lt => apply Nat.compare_lt_iff
   | |- Nat.compare _ _ = Gt => apply Nat.compare_gt_iff
   | |- Nat.eqb _ _ = true => apply Nat.eqb_eq
   | |- Nat.ltb _ _ = true => apply Nat.ltb_lt
   | |- Nat.leb _ _ = true => apply Nat.leb_le
   | |- Nat.ltb _ _ = false => apply notltb_le
   end) ;
omega.

Lemma ltb_S : forall n k, (n <? k) = (S n <? S k).
Proof.
intros n k.
symmetry ; case_eq (n <? k) ; intros Heq ; boolnat_omega.
Qed.


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




(** * Formulas *)

(** formulas *)
(** second-order formulas in the langage: true, conjunction, universal quantification *)
Inductive formula : Set :=
| var : vatom -> formula
| dvar : nat -> formula
| cst : atom -> formula
| top : formula
| wdg : formula -> formula -> formula
| frl : vatom -> formula -> formula.

(** size of formulas *)
Fixpoint fsize A : nat :=
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
induction A ; intros ; simpl ; auto ; try now (f_equal ; auto).
case_eq (n <? k) ; auto.
Qed.

Lemma fup_fup_com : forall k A,
  fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof.
induction A ; simpl ; auto ; try now (f_equal ; auto).
case_eq (n <? k) ; intros Heq ; rewrite <- ltb_S ; rewrite Heq ; auto.
Qed.

Hint Resolve fup_fup_com.

(** substitutes index [k] for variable [X] in [formula] [A] *)
Fixpoint mkn k X A :=
match A with
| var Y => if (beq_vat X Y) then dvar k else var Y
| dvar n => dvar n
| cst R => cst R
| top => top
| wdg B C => wdg (mkn k X B) (mkn k X C)
| frl Y B as C => if (beq_vat Y X) then C else frl Y (mkn k X B)
end.

Lemma fsize_mkn : forall k X A, fsize (mkn k X A) = fsize A.
Proof.
induction A ; intros ; simpl ; auto ; try now (f_equal ; auto).
- case_eq (beq_vat X v) ; auto.
- case_eq (beq_vat v X) ; simpl ; auto.
Qed.

Lemma fup_mkn_fup : forall k X A,
  fup (S k) (mkn 0 X (fup 0 A)) = mkn 0 X (fup 0 (fup k A)).
Proof.
induction A ; simpl ; auto ; try now (f_equal ; auto).
- case_eq (beq_vat X v) ; auto.
- case_eq (n <? k) ; intros Heq ; rewrite <- ltb_S ; rewrite Heq ; auto.
- case_eq (beq_vat v X) ; intros Heq ; simpl ; f_equal ; auto.
Qed.


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

Lemma fup_subs_com : forall k X F A,
  fup k (subs X F A) = subs X (fup k F) (fup k A).
Proof.
intros ; induction A ; simpl ; auto ; try now (f_equal ; auto).
- case_eq (beq_vat v X) ; intros Heq ; simpl ; f_equal ; auto.
- case_eq (n <? k) ; auto.
- case_eq (beq_vat v X) ; auto ; intros.
  simpl ; f_equal ; auto.
Qed.

Lemma subs_dvar_mkn : forall k X A, subs X (dvar k) A = mkn k X A.
Proof.
induction A ; simpl ; auto ; try now (f_equal ; auto).
- rewrite eqb_sym ; case_eq (beq_vat X v) ; intros ; simpl ; f_equal ; auto.
- case_eq (beq_vat v X) ; intros ; simpl ; f_equal ; auto.
Qed.





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

Lemma nsubs_fup_com : forall k n F A,
  nsubs (S (k + n)) (fup k F) (fup k A) = fup k (nsubs (k + n) F A).
Proof.
intros ; induction A ; simpl ; auto ; try now (f_equal ; auto).
case_eq ((k + n) ?= n0) ; case_eq (n0 <? k) ; case_eq (beq_nat n0 (S (k + n))) ;
  intros Heq1 Heq2 Heq3 ; simpl ;
  try rewrite Heq1 ; try rewrite Heq2 ; try rewrite Heq3 ; simpl ; auto ;
  try boolnat_omega.
- apply Nat.eqb_eq in Heq1 ; subst ; simpl.
  assert (k + n <? k = false) as Hle by boolnat_omega.
  rewrite Hle ; reflexivity.
- assert (pred n0 <? k = false) as Hle by boolnat_omega.
  rewrite Hle.
  destruct n0 ; simpl ; try boolnat_omega.
  reflexivity.
- destruct n0.
  + reflexivity.
  + assert (k + n ?= n0 = Gt) as Hle by boolnat_omega.
    rewrite Hle ; reflexivity.
Qed.

Fixpoint freevars A :=
match A with
| var X => X :: nil
| dvar _ => nil
| cst _ => nil
| top => nil
| wdg B C => (freevars B) ++ (freevars C)
| frl X B => remove vatomEq.eq_dec X (freevars B)
end.

Lemma in_freevars_frl : forall X Y, beq_vat Y X = false -> forall A,
  In X (freevars A) -> In X (freevars (frl Y A)).
Proof.
intros ; simpl.
remember (freevars A) as l.
revert H0 ; clear - H ; induction l ; intros Hi ; auto.
inversion Hi ; subst.
- simpl ; destruct (vatomEq.eq_dec Y X) ; subst.
  + rewrite eqb_refl in H ; inversion H.
  + constructor ; auto.
- simpl ; destruct (vatomEq.eq_dec Y a) ; subst ; auto.
  simpl ; right ; auto.
Qed.

Lemma freevars_fup : forall k F, freevars (fup k F) = freevars F.
Proof.
induction F ; intros ; simpl ; auto ; try now (f_equal ; auto).
case_eq (n <? k) ; auto.
Qed.

Lemma fup_closed : forall k F, freevars F = nil -> freevars (fup k F) = nil.
Proof.
intros ; rewrite freevars_fup ; assumption.
Qed.

Lemma freevars_nsubs : forall n F, freevars F = nil -> forall A,
  freevars (nsubs n F A) = freevars A.
Proof.
induction A ; intros ; simpl ; auto ; try now (f_equal ; auto).
case_eq (n ?= n0) ; auto.
Qed.

Lemma mkn_closed_l : forall k X F, ~ In X (freevars F) -> F = mkn k X F.
Proof.
induction F ; intros ; simpl ; auto.
- case_eq (beq_vat X v) ; auto ; intros.
  exfalso.
  apply vatomEq.eqb_eq in H0 ; subst.
  apply H ; constructor ; reflexivity.
- f_equal.
  + apply IHF1 ; intros Hf.
    apply H ; simpl.
    apply in_or_app ; left ; assumption.
  + apply IHF2 ; intros Hf.
    apply H ; simpl.
    apply in_or_app ; right ; assumption.
- case_eq (beq_vat v X) ; auto ; intros.
  f_equal ; apply IHF.
  intros Hf ; apply H ; simpl.
  remember (freevars F) as l.
  revert Hf ; clear - H0 ; induction l ; intros Hf ; auto.
  inversion Hf ; subst.
  + simpl ; destruct (vatomEq.eq_dec v X) ; subst.
    * rewrite eqb_refl in H0 ; inversion H0.
    * constructor ; auto.
  + simpl ; destruct (vatomEq.eq_dec v a) ; subst ; auto.
    simpl ; right ; auto.
Qed.

Lemma mkn_closed : forall k X F, freevars F = nil -> F = mkn k X F.
Proof.
intros ; apply mkn_closed_l.
intros Hf ; rewrite H in Hf ; inversion Hf.
Qed.

Lemma subs_closed_l : forall X F G, ~ In X (freevars F) -> F = subs X G F.
Proof.
induction F ; intros ; simpl ; auto.
- case_eq (beq_vat v X) ; auto ; intros.
  exfalso.
  apply vatomEq.eqb_eq in H0 ; subst.
  apply H ; constructor ; reflexivity.
- f_equal.
  + apply IHF1 ; intros Hf.
    apply H ; simpl.
    apply in_or_app ; left ; assumption.
  + apply IHF2 ; intros Hf.
    apply H ; simpl.
    apply in_or_app ; right ; assumption.
- case_eq (beq_vat v X) ; auto ; intros.
  f_equal ; apply IHF.
  intros Hf ; apply H.
  apply in_freevars_frl ;  assumption.
Qed.

Lemma subs_closed : forall X F G, freevars F = nil -> F = subs X G F.
Proof.
intros ; apply subs_closed_l.
intros Hf ; rewrite H in Hf ; inversion Hf.
Qed.

Lemma nsubs_mkn_com : forall X n F, freevars F = nil -> forall A,
  nsubs (S n) F (mkn 0 X A) = mkn 0 X (nsubs (S n) F A).
Proof.
intros ; induction A ; simpl ; auto.
- case_eq (beq_vat X v) ; intros Heq ; simpl ; auto.
- destruct n0 ; simpl.
  + reflexivity.
  + case_eq (n ?= n0) ; auto ; intros.
    apply mkn_closed ; assumption.
- f_equal ; auto.
- case_eq (beq_vat v X) ; auto.
  intros ; simpl ; f_equal ; auto.
Qed.

Lemma nsubs_subs_com : forall X F n G, freevars G = nil -> forall A,
  nsubs n G (subs X F A) = subs X (nsubs n G F) (nsubs n G A).
Proof.
intros ; induction A ; simpl ; auto ; try now (f_equal ; auto).
- case_eq (beq_vat v X) ; intros Heq ; simpl ; f_equal ; auto.
- case_eq (n ?= n0) ; auto ; intros.
  apply subs_closed ; auto.
- case_eq (beq_vat v X) ; auto ; intros.
  simpl ; f_equal ; auto.
Qed.

Lemma nsubs_z_fup : forall F A,
  nsubs 0 F (fup 0 A) = A.
Proof.
induction A ; simpl ; f_equal ; auto.
Qed.

Lemma nsubs_z_subs_fup : forall F X A,
  nsubs 0 F (mkn 0 X (fup 0 A)) = subs X F A.
Proof.
induction A ; simpl ; f_equal ; auto.
- rewrite eqb_sym.
  case_eq (beq_vat v X) ; intros Heq ; simpl ; f_equal ; auto.
- case_eq (beq_vat v X) ; intros Heq ; simpl ; f_equal ; auto.
  apply nsubs_z_fup.
Qed.

Lemma nfree_mkn : forall k X A, ~ In X (freevars A) -> mkn k X A = A.
Proof.
induction A ; intros ; simpl ; auto.
- case_eq (beq_vat X v) ; intros Heq ; auto.
  exfalso.
  apply vatomEq.eqb_eq in Heq ; subst.
  apply H ; constructor ; auto.
- f_equal.
  + apply IHA1.
    intros Hf ; apply H.
    apply in_or_app ; left ; assumption.
  + apply IHA2.
    intros Hf ; apply H.
    apply in_or_app ; right ; assumption.
- case_eq (beq_vat v X) ; intros Heq ; auto.
  f_equal.
  apply IHA.
  intros Hf ; apply H.
  apply in_freevars_frl ; assumption.
Qed.





(** * Proofs *)

(** Proofs *)
(** two-sided sequent calculus for second-order (additive) linear logic with connectives: 
    top, with, forall *)
Inductive prove : formula -> formula -> Set :=
| ax : forall A, prove A A
| topr : forall C, prove C top
| wdgr { C A B } : prove C A -> prove C B -> prove C (wdg A B)
| wdgll { A C } : forall B, prove A C -> prove (wdg A B) C
| wdglr { A C } : forall B, prove A C -> prove (wdg B A) C
| frlr { X C A } : prove (fup 0 C) (mkn 0 X (fup 0 A)) -> prove C (frl X A)
| frll { X A C } : forall F, freevars F = nil -> prove (subs X F A) C -> prove (frl X A) C.

(** substitutes [cterm] [u] for index [n] in proof [pi] and decreases indexes above [n] *)
Fixpoint psubs n F (Hc : freevars F = nil) {C A} (pi : prove C A) : prove (nsubs n F C) (nsubs n F A).
Proof.
destruct pi.
- apply ax.
- apply topr.
- simpl ; apply wdgr ; auto.
- simpl ; apply wdgll ; auto.
- simpl ; apply wdglr ; auto.
- rewrite <- (freevars_fup 0) in Hc.
  simpl ; apply frlr.
  change n with (0 + n) ; rewrite <- 2 nsubs_fup_com ; rewrite <- nsubs_mkn_com ; auto.
- simpl ; apply (frll (nsubs n F F0)).
  + rewrite freevars_nsubs ; assumption.
  + rewrite <- nsubs_subs_com ; auto.
Defined.

(** lift indexes above [k] in proof [pi] *)
Fixpoint pup k {C A} (pi : prove C A) : prove (fup k C) (fup k A) :=
match pi with
| ax _ => ax (fup _ _)
| topr _ => topr _
| wdgr pi1 pi2 => wdgr (pup _ pi1) (pup _ pi2)
| wdgll _ pi1 => wdgll _ (pup _ pi1)
| wdglr _ pi1 => wdglr _ (pup _ pi1)
| frlr pi1 => frlr (eq_rec _ (fun X => prove X _)
                             (eq_rec _ (fun X => prove _ X)
                                       (pup _ pi1) _
                                       (fup_mkn_fup _ _ _)) _
                             (fup_fup_com _ _))
| frll _ Hf pi1 => frll _ (fup_closed _ _ Hf) (eq_rec _ (fun X => prove X _)
                                                        (pup _ pi1) _
                                                        (fup_subs_com _ _ _ _))
end.



(** * Cut Elimination *)

(** height of proofs *)
Fixpoint psize {A B} (pi : prove A B) : nat :=
match pi with
| ax _ => 1
| topr _ => 1
| wdgr pi1 pi2 => S (max (psize pi1) (psize pi2))
| wdgll _ pi1 => S (psize pi1)
| wdglr _ pi1 => S (psize pi1)
| frlr pi1 => S (psize pi1)
| frll _ _ pi1 => S (psize pi1)
end.


Lemma psize_eq_recl_P : forall P (A B A' : formula) He (pi : prove (P A) B),
  psize (eq_rec A (fun X => prove (P X) B) pi A' He) = psize pi.
Proof.
destruct He ; reflexivity.
Qed.

Lemma psize_eq_recl : forall A B A' He (pi : prove A B),
  psize (eq_rec A (fun X => prove X B) pi A' He) = psize pi.
Proof.
destruct He ; reflexivity.
Qed.

Lemma psize_eq_recr_P : forall P (A B B' : formula) He (pi : prove A (P B)),
  psize (eq_rec B (fun X => prove A (P X)) pi B' He) = psize pi.
Proof.
destruct He ; reflexivity.
Qed.

Lemma psize_eq_recr : forall A B B' He (pi : prove A B),
  psize (eq_rec B (fun X => prove A X) pi B' He) = psize pi.
Proof.
destruct He ; reflexivity.
Qed.

Lemma psize_psubs : forall k F (Hf : freevars F = nil) {A B} (pi : prove A B),
  psize (psubs k F Hf pi) = psize pi.
Proof.
intros k F Hf A B pi.
revert k F Hf ; induction pi ; intros k F' Hf ; simpl ; auto.
- f_equal.
  rewrite psize_eq_recl.
  rewrite psize_eq_recr_P.
  rewrite psize_eq_recr.
  apply IHpi.
- f_equal.
  rewrite psize_eq_recl.
  apply IHpi.
Qed.

Lemma psize_pup : forall k {A B} (pi : prove A B), psize (pup k pi) = psize pi.
Proof.
intros k A B pi.
revert k ; induction pi ; intros k ; simpl ; auto.
- f_equal.
  rewrite psize_eq_recl.
  rewrite psize_eq_recr.
  apply IHpi.
- f_equal.
  rewrite psize_eq_recl.
  apply IHpi.
Qed.


(** Admissibility of the cut rule *)
Theorem cut_admiss : forall n, forall A B C (pi1 : prove A B) (pi2 : prove B C),
  n = psize pi1 + psize pi2 -> prove A C.
Proof.
induction n using (well_founded_induction lt_wf) ; intros ; subst.
assert (forall A B C (pi1' : prove A B) (pi2' : prove B C),
          psize pi1' + psize pi2' < psize pi1 + psize pi2 -> prove A C)
  as IH ; [ | clear H ].
{ intros ; eapply H ; [ eassumption | reflexivity ]. }
destruct pi2.
- apply pi1.
- apply topr.
- apply wdgr.
  + apply (IH _ _ _ pi1 pi2_1) ; simpl ; lia.
  + apply (IH _ _ _ pi1 pi2_2) ; simpl ; lia.
- cut (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                       psize pi1' + psize pi2' < psize pi1 + psize (wdgll B pi2) -> prove A1 C0),
         D = wdg A0 B -> prove A C) ; [ | clear ].
  { intros IH2 ; eapply IH2 ; [ eassumption | reflexivity ]. }
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  + apply wdgll ; assumption.
  + apply (IH _ _ _ pi1_1 pi2) ; simpl ; lia.
  + apply wdgll.
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
  + apply (frll F e).
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
- cut (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                       psize pi1' + psize pi2' < psize pi1 + psize (wdglr B pi2) -> prove A1 C0),
         D = wdg B A0 -> prove A C) ; [ | clear ].
  { intros IH2 ; eapply IH2 ; [ eassumption | reflexivity ]. }
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  + apply wdglr ; assumption.
  + apply (IH _ _ _ pi1_2 pi2) ; simpl ; lia.
  + apply wdgll.
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
  + apply (frll F e).
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
- apply frlr.
  apply (IH _ _ _ (pup 0 pi1) pi2).
  rewrite psize_pup ; simpl ; lia.
- cut (forall A D (pi1 : prove A D) X A0 C F e (pi2 : prove (subs X F A0) C)
              (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                       psize pi1' + psize pi2' < psize pi1 + psize (frll F e pi2) -> prove A1 C0),
         D = frl X A0 -> prove A C) ; [ | clear ].
  { intros IH2 ; eapply IH2 ; [ eassumption | reflexivity ]. }
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  + apply (frll F e) ; assumption.
  + apply wdgll.
    apply (IH _ _ _ pi1 (frll F e pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (frll F e pi2)) ; simpl ; lia.
  + remember (eq_rec _ (fun X => prove X _)
                       (eq_rec _ (fun X => prove _ X)
                                 (psubs 0 F e pi1) _
                                 (nsubs_z_subs_fup _ _ _)) _
                       (nsubs_z_fup _ _)) as pi1'.
    apply (IH _ _ _ pi1' pi2).
    rewrite Heqpi1'.
    rewrite psize_eq_recl.
    rewrite psize_eq_recr.
    rewrite psize_psubs.
    simpl ; lia.
 + apply (frll F e).
   apply (IH _ _ _ pi1 (frll F0 e0 pi2)) ; simpl ; lia.
Qed.



(** * Hilbert style properties *)

Lemma frl_elim : forall A F X, freevars F = nil -> prove (frl X A) (subs X F A).
Proof.
intros A F X Hf.
apply (frll F Hf).
apply ax.
Qed.

Lemma frl_wdg : forall A B X, prove (frl X (wdg A B)) (wdg (frl X A) (frl X B)).
Proof.
intros A B X.
apply wdgr.
- apply frlr ; simpl.
  apply (frll (dvar 0)) ; auto.
  simpl ; apply wdgll.
  rewrite subs_dvar_mkn.
  apply ax.
- apply frlr ; simpl.
  apply (frll (dvar 0)) ; auto.
  simpl ; apply wdglr.
  rewrite subs_dvar_mkn.
  apply ax.
Qed.

Lemma frl_nfree : forall A X, ~ In X (freevars A) -> prove A (frl X A).
Proof.
intros A X Hnf.
apply frlr.
rewrite nfree_mkn.
- apply ax.
- intros Hf ; apply Hnf.
  rewrite freevars_fup in Hf ; assumption.
Qed.


(** * Other properties *)

(** Axiom expansion *)
Lemma ax_exp : forall A, prove A A.
Proof.
assert (forall n A, fsize A = n -> prove A A) as Hn.
{ induction n using (well_founded_induction lt_wf) ; intros ; subst.
  destruct A.
  - apply ax.
  - apply ax.
  - apply ax.
  - apply topr.
  - apply wdgr ; [ apply wdgll | apply wdglr ] ; (eapply H ; [ | reflexivity ]) ; simpl ; omega.
  - apply frlr.
    simpl ; apply (frll (dvar 0)) ; auto.
    rewrite subs_dvar_mkn.
    eapply H ; [ | reflexivity ].
    rewrite fsize_mkn ; rewrite fsize_fup ; simpl ; omega. }
intros A ; eapply Hn ; reflexivity.
Qed.



