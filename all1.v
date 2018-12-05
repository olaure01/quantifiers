(* Sequent Calculus for First-Order Additive Linear Logic *)

Require Import Wf_nat.
Require Import Lia.

Require Import fot.

(** * Formulas *)

Parameter atom : Set.  (* propositional variables for [formula] *)

(** formulas *)
(** first-order formulas in the langage: true, conjunction, universal quantification *)
Inductive formula : Set :=
| var : atom -> list term -> formula
| top : formula
| wdg : formula -> formula -> formula
| frl : vatom -> formula -> formula.

Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | | A1 A2 | xx A ] ; simpl ; intros ;
  [ try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; intuition ;
                       rewrite IHll ; f_equal ; intuition)
  | auto
  | try (f_equal ; intuition)
  | try (f_equal ; intuition) ] ; try ((rnow idtac) ; fail) ; try (rcauto ; fail).


(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X l => var X (map (tup k) l)
| top => top
| wdg B C => wdg (fup k B) (fup k C)
| frl x B => frl x (fup k B)
end.

Lemma fup_fup_com : forall k A,
  fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof. formula_induction A. Qed.
Hint Rewrite fup_fup_com.


(** substitutes [term] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint subs x u A :=
match A with
| var X l => var X (map (tsubs x u) l)
| top => top
| wdg B C => wdg (subs x u B) (subs x u C)
| frl y B as C => if (beq_vat y x) then C else frl y (subs x u B)
end.

Lemma fup_subs_com : forall k x u A,
  fup k (subs x u A) = subs x (tup k u) (fup k A).
Proof. formula_induction A.
rnow case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal.
Qed.
Hint Rewrite fup_subs_com.

(** substitutes [term] [u] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint nsubs n u A :=
match A with
| var X l => var X (map (ntsubs n u) l)
| top => top
| wdg B C => wdg (nsubs n u B) (nsubs n u C)
| frl x B => frl x (nsubs n u B)
end.

Lemma nsubs_fup_com : forall k u A,
  nsubs (S k) (tup 0 u) (fup 0 A) = fup 0 (nsubs k u A).
Proof. formula_induction A. Qed.
Hint Rewrite nsubs_fup_com.

Lemma nsubs_z_fup : forall u A, nsubs 0 u (fup 0 A) = A.
Proof. formula_induction A. Qed.
Hint Rewrite nsubs_z_fup.

Lemma nsubs_subs_com : forall x v n u, ~ In x (freevars u) -> forall A,
  nsubs n u (subs x v A) = subs x (ntsubs n u v) (nsubs n u A).
Proof. now formula_induction A ; rcauto ; f_equal. Qed.
Hint Rewrite nsubs_subs_com using try (intuition ; fail) ;
                                  (try apply closed_nofreevars) ; intuition ; fail.


(** size of formulas *)
Fixpoint fsize A :=
match A with
| var _ _ => 1
| top => 1
| wdg B C => S (fsize B + fsize C)
| frl _ B => S (fsize B)
end.

Lemma fsize_fup : forall k A, fsize (fup k A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_fup.

Lemma fsize_subs : forall u x A, fsize (subs x u A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_subs.



(** * Proofs *)

Notation fupz := (fup 0).

(** Proofs *)
(** two-sided sequent calculus for first-order (additive) linear logic with connectives: 
    top, with, forall *)
Inductive prove : formula -> formula -> Set :=
| ax : forall A, prove A A
| topr : forall C, prove C top
| wdgr { C A B } : prove C A -> prove C B -> prove C (wdg A B)
| wdgll { A C } : forall B, prove A C -> prove (wdg A B) C
| wdglr { A C } : forall B, prove A C -> prove (wdg B A) C
| frlr { x C A } : prove (fupz C) (subs x (dvar 0) (fupz A)) -> prove C (frl x A)
| frll { x A C } : forall u, closed u -> prove (subs x u A) C -> prove (frl x A) C.
Hint Constructors prove.

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

(** substitutes [cterm] [u] for index [n] in proof [pi] and decreases indexes above [n] *)
Theorem psubs n u (Hc : closed u) {C A} (pi : prove C A) :
  { pi' : prove (nsubs n u C) (nsubs n u A) | psize pi' = psize pi }.
Proof with try assumption.
revert n u Hc ; induction pi ; intros n u' Hc ;
  try (destruct (IHpi n u') as [pi' Hs]) ;
  try (destruct (IHpi1 n u') as [pi1' Hs1]) ;
  try (destruct (IHpi2 n u') as [pi2' Hs2])...
- now exists (ax _).
- now exists (topr _).
- exists (wdgr pi1' pi2') ; simpl ; auto.
- exists (wdgll _ pi') ; simpl ; auto.
- exists (wdglr _ pi') ; simpl ; auto.
- clear pi' Hs.
  rewrite <- (freevars_tup 0) in Hc.
  destruct (IHpi (S n) (tup 0 u')) as [pi' Hs]...
  simpl ; rewrite <- Hs ; clear Hs.
  revert pi' ; autorewrite with core.
  intros pi' ; exists (frlr pi') ; reflexivity.
- simpl ; rewrite <- Hs ; clear Hs.
  revert pi' ; autorewrite with core.
  rewrite <- (freevars_ntsubs n u' Hc) in e.
  intros pi' ; exists (frll _ e pi') ; reflexivity.
Qed.

(** lift indexes above [k] in proof [pi] *)
Theorem pup k {C A} (pi : prove C A) :
  { pi' : prove (fup k C) (fup k A) | psize pi' = psize pi }.
Proof with autorewrite with core.
revert k ; induction pi ; intros k ;
  try (destruct (IHpi k) as [pi' Hs]) ;
  try (destruct (IHpi1 k) as [pi1' Hs1]) ;
  try (destruct (IHpi2 k) as [pi2' Hs2]).
- now exists (ax _).
- now exists (topr _).
- exists (wdgr pi1' pi2') ; simpl ; auto.
- exists (wdgll _ pi') ; simpl ; auto.
- exists (wdglr _ pi') ; simpl ; auto.
- clear pi' Hs.
  destruct (IHpi (S k)) as [pi' Hs].
  simpl ; rewrite <- Hs ; clear Hs.
  revert pi'.
  change (dvar 0) with (tup (S k) (dvar 0))...
  intros pi' ; exists (frlr pi') ; reflexivity.
- simpl ; rewrite <- Hs ; clear Hs.
  revert pi'...
  rewrite <- (freevars_tup k) in e.
  intros pi' ; exists (frll _ e pi') ; reflexivity.
Qed.


(** * Cut Elimination *)

Theorem cutr : forall A B C (pi1 : prove A B) (pi2 : prove B C), prove A C.
Proof with try assumption ; try lia.
enough (forall n, forall A B C (pi1 : prove A B) (pi2 : prove B C),
          n = psize pi1 + psize pi2 -> prove A C)
  by (intros ; apply (H _ _ _ _ pi1 pi2 eq_refl)).
induction n using (well_founded_induction lt_wf) ; intros ; subst.
assert (IH : forall A B C (pi1' : prove A B) (pi2' : prove B C),
               psize pi1' + psize pi2' < psize pi1 + psize pi2 -> prove A C)
  by (intros ; eapply H ; [ eassumption | reflexivity ]) ; clear H.
destruct pi2 ; intuition.
- apply wdgr.
  + apply (IH _ _ _ pi1 pi2_1) ; simpl...
  + apply (IH _ _ _ pi1 pi2_2) ; simpl...
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                psize pi1' + psize pi2' < psize pi1 + psize (wdgll B pi2) -> prove A1 C0),
         D = wdg A0 B -> prove A C)
    as IH2 by (eapply IH2 ; [ eassumption | reflexivity ]) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst ;
    try (constructor ; apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia).
  + apply wdgll...
  + apply (IH _ _ _ pi1_1 pi2) ; simpl...
  + apply (frll u)...
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl...
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (wdglr B pi2) -> prove A1 C0),
         D = wdg B A0 -> prove A C)
    as IH2 by (eapply IH2 ; [ eassumption | reflexivity ]) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst ;
    try (constructor ; apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia).
  + apply wdglr...
  + apply (IH _ _ _ pi1_2 pi2) ; simpl...
  + apply (frll u)...
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl...
- destruct (pup 0 pi1) as [pi1' Hs].
  apply frlr.
  apply (IH _ _ _ pi1' pi2) ; simpl...
- enough (forall A D (pi1 : prove A D) x A0 C u e (pi2 : prove (subs x u A0) C)
              (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (frll u e pi2) -> prove A1 C0),
         D = frl x A0 -> prove A C)
    as IH2 by (eapply IH2 ; [ eassumption | reflexivity ]) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst ;
    try (constructor ; apply (IH _ _ _ pi1 (frll _ e pi2)) ; simpl ; lia).
  + apply (frll u) ; assumption.
  + destruct (psubs 0 u e pi1) as [pi1' Hs].
    simpl in IH ; rewrite <- Hs in IH ; clear Hs.
    revert pi1' IH ; autorewrite with core.
    intros pi1' IH ; apply (IH _ _ _ pi1' pi2) ; simpl...
  + apply (frll u)...
    apply (IH _ _ _ pi1 (frll _ e0 pi2)) ; simpl...
Qed.


(** * Free variables in [formula] *)
Fixpoint ffreevars A :=
match A with
| var _ l => concat (map freevars l)
| top => nil
| wdg B C => (ffreevars B) ++ (ffreevars C)
| frl x B => remove vatomEq.eq_dec x (ffreevars B)
end.

Lemma in_ffreevars_frl : forall x y, beq_vat y x = false -> forall A,
  In x (ffreevars A) -> In x (ffreevars (frl y A)).
Proof.
intros x y Heq A Hi ; simpl ; remember (ffreevars A) as l.
revert Hi ; clear - Heq ; induction l ; intros Hi ; auto.
inversion Hi ; subst ; simpl ; rcauto.
exfalso ; subst ; rewrite eqb_refl in Heq ; inversion Heq.
Qed.

Lemma ffreevars_fup : forall k A, ffreevars (fup k A) = ffreevars A.
Proof. formula_induction A. Qed.
Hint Rewrite ffreevars_fup.

Lemma nfree_subs : forall x u A, ~ In x (ffreevars A) -> subs x u A = A.
Proof. formula_induction A ; try rcauto.
- rnow apply nfree_tsubs then apply H.
- rnow apply H.
- rnow rewrite IHA.
  now apply H ; apply in_ffreevars_frl.
Qed.
Hint Rewrite nfree_subs using intuition ; fail.


(** * Hilbert style properties *)

Lemma frl_elim : forall A u x, closed u -> prove (frl x A) (subs x u A).
Proof.
intros A u x Hc.
now apply (frll u).
Qed.

Lemma frl_wdg : forall A B x, prove (frl x (wdg A B)) (wdg (frl x A) (frl x B)).
Proof.
intros A B x.
repeat constructor ; simpl ;
  now (apply (frll (dvar 0)) ; constructor).
Qed.

Lemma frl_nfree : forall A x, ~ In x (ffreevars A) -> prove A (frl x A).
Proof. 
intros A X Hnf.
rewrite <- (ffreevars_fup 0) in Hnf.
rnow apply frlr.
Qed.


(** * Other properties *)

(** Axiom expansion *)
Lemma ax_exp : forall A, prove A A.
Proof.
enough (Hn : forall n A, fsize A = n -> prove A A)
  by (intros A ; eapply Hn ; reflexivity).
induction n using (well_founded_induction lt_wf) ; intros ; subst.
destruct A.
- apply ax.
- apply topr.
- apply wdgr ; [ apply wdgll | apply wdglr ] ; (eapply H ; [ | reflexivity ]) ; simpl ; lia.
- apply frlr.
  simpl ; apply (frll (dvar 0)) ; auto.
Qed.



