Require Import PeanoNat.
Require Import Wf_nat.
Require Import Lia.
Require Import List.
Require Import Equalities.


(** * Preliminaries *)

Lemma Forall_eq_map {A B : Type} : forall (f g : A -> B) l,
  Forall (fun x => f x = g x) l -> map f l = map g l.
Proof.
intros f g l.
induction l ; intros Heq.
- reflexivity.
- inversion Heq.
  simpl ; f_equal.
  + assumption.
  + apply IHl ; assumption.
Qed.



(** * Different kinds of atoms *)

Parameter atom : Set.  (* propositional variables for [formula] *)
Parameter tatom : Set. (* function symbols for [term] *)
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


(** * Terms *)

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
(** [dvar] for De Bruijn style eigen variables in proofs *)
(** [tvar] for quantified variables in formulas *)
Inductive term : Set :=
| dvar : nat -> term
| tvar : vatom -> term
| tconstr : tatom -> list term -> term.

(** appropriate induction for [term] (with list inside): so called "nested fix" *)
Fixpoint term_ind_list t :
  forall P : term -> Prop,
  forall Pl : list term -> Prop,
  (Pl nil) ->
  (forall t l, P t -> Pl l -> Pl (t :: l)) ->
  (forall n, P (dvar n)) ->
  (forall x, P (tvar x)) ->
  (forall f l, Pl l -> P (tconstr f l)) -> P t :=
fun P Pl Plnil Plcons Pdvar Ptvar Pconstr =>
match t with
| dvar n => Pdvar n
| tvar x => Ptvar x
| tconstr c l => Pconstr c l
    ((fix l_ind l' : Pl l' :=
      match l' with
     | nil => Plnil
     | cons t1 l1 => Plcons t1 l1
                       (term_ind_list t1 P Pl Plnil Plcons Pdvar Ptvar Pconstr)
                       (l_ind l1)
     end) l)
end.
Definition term_ind_list_Forall u :
  forall P : term -> Prop,
  (forall n, P (dvar n)) ->
  (forall x, P (tvar x)) ->
  (forall f l, Forall P l -> P (tconstr f l)) -> P u.
Proof.
intros P Pdvar Ptvar Pconstr.
eapply term_ind_list.
- apply Forall_nil.
- apply Forall_cons.
- apply Pdvar.
- apply Ptvar.
- apply Pconstr.
Defined.
Ltac term_induction t :=
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  apply (term_ind_list_Forall t) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; try (simpl ; f_equal) ; repeat (rewrite map_map) ;
    try apply Forall_eq_map ; try assumption].


(** lift indexes above [k] in [term] [t] *)
Fixpoint tup k t :=
match t with
| dvar n => if n <? k then dvar n else dvar (S n)
| tvar x => tvar x
| tconstr f l => tconstr f (map (tup k) l)
end.

Lemma tup_tup_com : forall k t,
  tup (S k) (tup 0 t) = tup 0 (tup k t).
Proof.
intros ; term_induction t.
change (S n <? S k) with (n <? k) ; case_eq (n <? k) ; auto.
Qed.



(** closed terms *)
Inductive cterm : Set :=
| cdvar : nat -> cterm
| cconstr : tatom -> list cterm -> cterm.

(** appropriate induction for [cterm] (with list inside) :so called "nested fix" *)
Fixpoint cterm_ind_list u :
  forall P : cterm -> Prop,
  forall Pl : list cterm -> Prop,
  (Pl nil) ->
  (forall v l, P v -> Pl l -> Pl (v :: l)) ->
  (forall n, P (cdvar n)) ->
  (forall f l, Pl l -> P (cconstr f l)) -> P u :=
fun P Pl Plnil Plcons Pdvar Pconstr =>
match u with
| cdvar n => Pdvar n
| cconstr c l => Pconstr c l
    ((fix l_ind l' : Pl l' :=
      match l' with
     | nil => Plnil
     | cons t1 l1 => Plcons t1 l1
                       (cterm_ind_list t1 P Pl Plnil Plcons Pdvar Pconstr)
                       (l_ind l1)
     end) l)
end.
Definition cterm_ind_list_Forall u :
  forall P : cterm -> Prop,
  (forall n, P (cdvar n)) ->
  (forall f l, Forall P l -> P (cconstr f l)) -> P u.
Proof.
intros P Pdvar Pconstr.
eapply cterm_ind_list.
- apply Forall_nil.
- apply Forall_cons.
- apply Pdvar.
- apply Pconstr.
Defined.
Ltac cterm_induction u :=
  let nn := fresh "n" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  apply (cterm_ind_list_Forall u) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros c l IHl ; try (simpl ; f_equal) ; repeat (rewrite map_map) ;
    try apply Forall_eq_map ; try assumption].


(** inclusion of [cterm] in [term] *)
Fixpoint cterm_to_term u :=
match u with
| cdvar n => dvar n
| cconstr f l => tconstr f (map cterm_to_term l)
end.

(** lift indexes above [k] in [cterm] [u] *)
Fixpoint cup k u :=
match u with
| cdvar n => if (n <? k) then cdvar n else cdvar (S n)
| cconstr c l => cconstr c (map (cup k) l)
end.

Lemma cup_tup : forall k u,
  cterm_to_term (cup k u) = tup k (cterm_to_term u).
Proof.
intros ; cterm_induction u.
case_eq (n <? k) ; auto.
Qed.



(** * Term substitutions *)

(** substitutes [cterm] [u] for index [n] in [cterm] [v] and decreases indexes above [n] *)
Fixpoint ncsubs n u v :=
match v with
| cdvar k => match n ?= k with
             | Eq => u
             | Lt => cdvar (pred k)
             | Gt => cdvar k
             end
| cconstr f l => cconstr f (map (ncsubs n u) l)
end.

(** substitutes [cterm] [u] for variable [x] in [term] [t] *)
Fixpoint tsubs x u t :=
match t with
| tvar y => if (beq_vat y x) then (cterm_to_term u) else tvar y
| tconstr c l => tconstr c (map (tsubs x u) l)
| _ as t' => t'
end.

Lemma tsubs_cterm : forall x v u,
  tsubs x v (cterm_to_term u) = cterm_to_term u.
Proof.
intros ; cterm_induction u.
Qed.

Hint Resolve cup_tup.

Lemma tup_tsubs_com : forall k x u t,
  tup k (tsubs x u t) = tsubs x (cup k u) (tup k t).
Proof.
intros ; term_induction t.
- case_eq (n <? k) ; auto.
- case_eq (beq_vat x0 x) ; auto.
Qed.

(** substitutes [cterm] [u] for index [n] in [term] [t] and decreases indexes above [n] *)
Fixpoint ntsubs n u t :=
match t with
| dvar k => match n ?= k with
            | Eq => cterm_to_term u
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| tconstr f l => tconstr f (map (ntsubs n u) l)
| _ as t' => t'
end.

Lemma ntsubs_cterm : forall n v u,
  ntsubs n v (cterm_to_term u) = cterm_to_term (ncsubs n v u).
Proof.
intros ; cterm_induction u.
case_eq (n ?= n0) ; auto.
Qed.

Hint Resolve tsubs_cterm ntsubs_cterm.

Lemma ntsubs_tup_com : forall k u t,
  ntsubs (S k) (cup 0 u) (tup 0 t) = tup 0 (ntsubs k u t).
Proof.
intros ; term_induction t.
case_eq (k ?= n) ; auto.
intros Heq ; destruct n ; auto.
exfalso ; destruct k ; inversion Heq.
Qed.

Lemma ntsubs_tsubs_com : forall x v n u t,
  ntsubs n u (tsubs x v t) = tsubs x (ncsubs n u v) (ntsubs n u t).
Proof.
intros ; term_induction t.
- case_eq (n ?= n0) ; auto.
- case_eq (beq_vat x0 x) ; auto.
Qed.

Lemma tsubs_z_ntsubs_com : forall x n u t,
  tsubs x (cdvar 0) (ntsubs (S n) u t) = ntsubs (S n) u (tsubs x (cdvar 0) t).
Proof.
intros ; term_induction t ;
  try now (case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal ; auto).
destruct n0 ; auto.
case_eq (n ?= n0) ; auto.
Qed.

Hint Resolve tup_tup_com tup_tsubs_com ntsubs_tup_com ntsubs_tsubs_com tsubs_z_ntsubs_com.



(** * Formulas *)

(** formulas *)
(** first-order formulas in the langage: true, conjunction, universal quantification *)
Inductive formula : Set :=
| var : atom -> list term -> formula
| top : formula
| wdg : formula -> formula -> formula
| frl : vatom -> formula -> formula.

Ltac formula_induction A :=
  let XX := fresh "X" in
  let xx := fresh "x" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let ll2 := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | | A1 A2 | xx A ] ; simpl ;
  [ try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; intuition ;
                       rewrite IHll ; f_equal ; intuition)
  | auto
  | try (f_equal ; intuition)
  | try (f_equal ; intuition) ].

(** size of formulas *)
Fixpoint fsize A :=
match A with
| var _ _ => 1
| top => 1
| wdg B C => S (fsize B + fsize C)
| frl _ B => S (fsize B)
end.


(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X l => var X (map (tup k) l)
| top => top
| wdg B C => wdg (fup k B) (fup k C)
| frl x B => frl x (fup k B)
end.

Lemma fsize_fup : forall k A, fsize (fup k A) = fsize A.
Proof.
formula_induction A.
Qed.

Lemma fup_fup_com : forall k A,
  fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof.
intros ; formula_induction A.
Qed.


(** substitutes [cterm] [u] for variable [x] in [formula] [A] *)
Fixpoint subs x u A :=
match A with
| var X l => var X (map (tsubs x u) l)
| top => top
| wdg B C => wdg (subs x u B) (subs x u C)
| frl y B as C => if (beq_vat y x) then C else frl y (subs x u B)
end.

Lemma fsize_subs_cdvar : forall k X A, fsize (subs X (cdvar k) A) = fsize A.
Proof.
intros k X ; formula_induction A.
case_eq (beq_vat x X) ; simpl ; auto.
Qed.

Lemma fup_subs_com : forall k x u A,
  fup k (subs x u A) = subs x (cup k u) (fup k A).
Proof.
intros ; formula_induction A.
case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal ; auto.
Qed.

(** substitutes [cterm] [u] for index [n] in [formula] [A] *)
Fixpoint nsubs n u A :=
match A with
| var X l => var X (map (ntsubs n u) l)
| top => top
| wdg B C => wdg (nsubs n u B) (nsubs n u C)
| frl x B as C => frl x (nsubs n u B)
end.

Lemma nsubs_fup_com : forall k u A,
  nsubs (S k) (cup 0 u) (fup 0 A) = fup 0 (nsubs k u A).
Proof.
intros ; formula_induction A.
Qed.

Lemma nsubs_subs_com : forall x v n u A,
  nsubs n u (subs x v A) = subs x (ncsubs n u v) (nsubs n u A).
Proof.
intros ; formula_induction A.
case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal ; auto.
Qed.

Lemma subs_z_nsubs_com : forall x n u A,
  subs x (cdvar 0) (nsubs (S n) u A) = nsubs (S n) u (subs x (cdvar 0) A).
Proof.
intros ; induction A ; simpl ; f_equal ; intuition ;
  try now (case_eq (beq_vat v x) ; intros ; simpl ; f_equal ; auto).
induction l ; auto.
simpl ; rewrite IHl ; f_equal ; auto.
Qed.

Lemma ntsubs_z_tup : forall u t, ntsubs 0 u (tup 0 t) = t.
Proof.
intros ; term_induction t.
induction l ; auto.
inversion IHl ; subst ; simpl ; f_equal ; auto.
Qed.

Hint Resolve ntsubs_z_tup.

Lemma nsubs_z_fup : forall u A, nsubs 0 u (fup 0 A) = A.
Proof.
intros ; formula_induction A.
Qed.

Lemma ntsubs_z_tsubs_tup : forall u x t,
  ntsubs 0 u (tsubs x (cdvar 0) (tup 0 t)) = tsubs x u t.
Proof.
intros ; term_induction t.
case_eq (beq_vat x0 x) ; simpl ; auto.
Qed.

Hint Resolve nsubs_z_fup ntsubs_z_tsubs_tup.

Lemma nsubs_z_subs_fup : forall u x A,
  nsubs 0 u (subs x (cdvar 0) (fup 0 A)) = subs x u A.
Proof.
intros ; formula_induction A.
case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal ; auto.
Qed.





(** * Proofs *)

(** Proofs *)
(** two-sided sequent calculus for first-order (additive) linear logic with connectives: 
    top, with, forall *)
Inductive prove : formula -> formula -> Set :=
| ax : forall A, prove A A
| topr : forall C, prove C top
| wdgr { C A B } : prove C A -> prove C B -> prove C (wdg A B)
| wdgll { A C } : forall B, prove A C -> prove (wdg A B) C
| wdglr { A C } : forall B, prove A C -> prove (wdg B A) C
| frlr { x C A } : prove (fup 0 C) (subs x (cdvar 0) (fup 0 A)) -> prove C (frl x A)
| frll { x A C } : forall u, prove (subs x u A) C -> prove (frl x A) C.

(** height of proofs *)
Fixpoint psize {A B} (pi : prove A B) : nat :=
match pi with
| ax _ => 1
| topr _ => 1
| wdgr pi1 pi2 => S (max (psize pi1) (psize pi2))
| wdgll _ pi1 => S (psize pi1)
| wdglr _ pi1 => S (psize pi1)
| frlr pi1 => S (psize pi1)
| frll _ pi1 => S (psize pi1)
end.

(** substitutes [cterm] [u] for index [n] in proof [pi] and decreases indexes above [n] *)
Theorem psubs n u {C A} (pi : prove C A) :
  { pi' : prove (nsubs n u C) (nsubs n u A) | psize pi' = psize pi }.
Proof with try assumption.
revert n u ; induction pi ; intros n u' ;
  try (destruct (IHpi n u') as [pi' Hs]) ;
  try (destruct (IHpi1 n u') as [pi1' Hs1]) ;
  try (destruct (IHpi2 n u') as [pi2' Hs2]).
- exists (ax _) ; auto.
- exists (topr _) ; auto.
- exists (wdgr pi1' pi2') ; simpl ; auto.
- exists (wdgll _ pi') ; simpl ; auto.
- exists (wdglr _ pi') ; simpl ; auto.
- clear pi' Hs.
  destruct (IHpi (S n) (cup 0 u')) as [pi' Hs].
  simpl ; rewrite <- Hs ; clear Hs.
  revert pi'.
  rewrite <- subs_z_nsubs_com...
  rewrite 2 nsubs_fup_com.
  intros pi' ; exists (frlr pi') ; reflexivity.
- simpl ; rewrite <- Hs ; clear Hs.
  revert pi' ; rewrite nsubs_subs_com...
  intros pi' ; exists (frll (ncsubs n u' u) pi') ; reflexivity.
Qed.

(** lift indexes above [k] in proof [pi] *)
Theorem pup k {C A} (pi : prove C A) :
  { pi' : prove (fup k C) (fup k A) | psize pi' = psize pi }.
Proof.
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
  change (dvar 0) with (fup (S k) (dvar 0)).
  rewrite fup_subs_com.
  rewrite 2 fup_fup_com.
  intros pi' ; exists (frlr pi') ; reflexivity.
- simpl ; rewrite <- Hs ; clear Hs.
  revert pi'.
  rewrite fup_subs_com.
  intros pi' ; exists (frll (cup k u) pi') ; reflexivity.
Qed.


(** * Cut Elimination *)

Theorem cutr : forall A B C (pi1 : prove A B) (pi2 : prove B C), prove A C.
Proof.
enough (forall n, forall A B C (pi1 : prove A B) (pi2 : prove B C),
          n = psize pi1 + psize pi2 -> prove A C)
  by (intros ; apply (H _ _ _ _ pi1 pi2 eq_refl)).
induction n using (well_founded_induction lt_wf) ; intros ; subst.
assert (IH : forall A B C (pi1' : prove A B) (pi2' : prove B C),
               psize pi1' + psize pi2' < psize pi1 + psize pi2 -> prove A C)
  by (intros ; eapply H ; [ eassumption | reflexivity ]) ; clear H.
destruct pi2.
- apply pi1.
- apply topr.
- apply wdgr.
  + apply (IH _ _ _ pi1 pi2_1) ; simpl ; lia.
  + apply (IH _ _ _ pi1 pi2_2) ; simpl ; lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                psize pi1' + psize pi2' < psize pi1 + psize (wdgll B pi2) -> prove A1 C0),
         D = wdg A0 B -> prove A C)
    as IH2 by (eapply IH2 ; [ eassumption | reflexivity ]) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  + apply wdgll ; assumption.
  + apply (IH _ _ _ pi1_1 pi2) ; simpl ; lia.
  + apply wdgll.
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
  + apply (frll u).
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (wdglr B pi2) -> prove A1 C0),
         D = wdg B A0 -> prove A C)
    as IH2 by (eapply IH2 ; [ eassumption | reflexivity ]) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  + apply wdglr ; assumption.
  + apply (IH _ _ _ pi1_2 pi2) ; simpl ; lia.
  + apply wdgll.
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
  + apply (frll u).
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
- apply frlr.
  destruct (pup 0 pi1) as [pi1' Hs].
  apply (IH _ _ _ pi1' pi2) ; simpl ; lia.
- enough (forall A D (pi1 : prove A D) x A0 C u (pi2 : prove (subs x u A0) C)
              (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (frll u pi2) -> prove A1 C0),
         D = frl x A0 -> prove A C)
    as IH2 by (eapply IH2 ; [ eassumption | reflexivity ]) ; clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  + apply (frll u) ; assumption.
  + apply wdgll.
    apply (IH _ _ _ pi1 (frll _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (frll _ pi2)) ; simpl ; lia.
  + destruct (psubs 0 u pi1) as [pi1' Hs].
    simpl in IH ; rewrite <- Hs in IH ; clear Hs.
    revert pi1' IH.
    rewrite nsubs_z_subs_fup.
    rewrite nsubs_z_fup.
    intros pi1' IH ; apply (IH _ _ _ pi1' pi2) ; lia.
  + apply (frll u).
    apply (IH _ _ _ pi1 (frll _ pi2)) ; simpl ; lia.
Qed.



(** * Free variables *)
Fixpoint tfreevars t :=
match t with
| dvar _ => nil
| tvar x => x :: nil
| tconstr c l => fold_right (fun x s => app (tfreevars x) s)  nil l
end.

Lemma tfreevars_tup : forall k t, tfreevars (tup k t) = tfreevars t.
Proof.
intros k t ; revert k ; term_induction t ; intros.
- case_eq (n <? k) ; auto.
- induction l ; intuition.
  inversion IHl ; subst ; simpl ; f_equal ; intuition.
Qed.

Lemma nfree_tsubs : forall x u t, ~ In x (tfreevars t) -> tsubs x u t = t.
Proof.
intros x u t ; term_induction t ; simpl ; intuition ; f_equal ; intuition.
- case_eq (beq_vat x0 x) ; intuition.
  exfalso ; apply vatomEq.eqb_eq in H ; intuition.
- induction l ; intuition.
  inversion IHl ; subst ; simpl ; f_equal.
  + apply H2.
    intros Hf' ; apply H ; simpl ; intuition.
  + apply IHl0 ; intuition.
    apply H ; simpl ; intuition.
Qed.

Fixpoint freevars A :=
match A with
| var _ l => fold_right (fun x s => app (tfreevars x) s)  nil l
| top => nil
| wdg B C => (freevars B) ++ (freevars C)
| frl X B => remove vatomEq.eq_dec X (freevars B)
end.

Lemma in_freevars_frl : forall x y, beq_vat y x = false -> forall A,
  In x (freevars A) -> In x (freevars (frl y A)).
Proof.
intros ; simpl.
remember (freevars A) as l.
revert H0 ; clear - H ; induction l ; intros Hi ; auto.
inversion Hi ; subst.
- simpl ; destruct (vatomEq.eq_dec y x) ; intuition.
  subst ; rewrite eqb_refl in H ; inversion H.
- simpl ; destruct (vatomEq.eq_dec y a) ; intuition.
Qed.

Lemma freevars_fup : forall k A, freevars (fup k A) = freevars A.
Proof.
intros k A ; revert k ; formula_induction A. 
- apply tfreevars_tup.
- f_equal ; intuition.
- rewrite IHA ; reflexivity.
Qed.

Lemma nfree_subs : forall X F A, ~ In X (freevars A) -> subs X F A = A.
Proof.
induction A ; simpl ; intuition ; f_equal ; intuition.
- induction l ; intuition.
  simpl ; f_equal.
  + apply nfree_tsubs.
    intros Hf ; apply H ; simpl ; intuition.
  + apply IHl ; intros Hf ; apply H ; simpl ; intuition.
- case_eq (beq_vat v X) ; intuition.
  f_equal ; apply IHA.
  intros Hf ; apply H ; apply in_freevars_frl ; assumption.
Qed.




(** * Hilbert style properties *)

Lemma frl_elim : forall A u x, prove (frl x A) (subs x u A).
Proof.
intros A u x.
apply (frll u).
apply ax.
Qed.

Lemma frl_wdg : forall A B x, prove (frl x (wdg A B)) (wdg (frl x A) (frl x B)).
Proof.
intros A B x.
apply wdgr.
- apply frlr ; simpl.
  apply (frll (cdvar 0)) ; simpl.
  apply wdgll.
  apply ax.
- apply frlr ; simpl.
  apply (frll (cdvar 0)) ; simpl.
  apply wdglr.
  apply ax.
Qed.

Lemma frl_nfree : forall A x, ~ In x (freevars A) -> prove A (frl x A).
Proof.
intros A x Hnf.
apply frlr.
rewrite nfree_subs.
- apply ax.
- intros Hf ; apply Hnf.
  rewrite freevars_fup in Hf ; assumption.
Qed.



(** * Other properties *)

(** Axiom expansion *)
Lemma ax_exp : forall A, prove A A.
Proof.
enough (Hn : forall n A, fsize A = n -> prove A A)
  by (intros A ; eapply Hn ; reflexivity).
induction n using (well_founded_induction lt_wf) ; intros ; subst.
(* destruct A ; try now constructor. *)
destruct A.
- apply ax.
- apply topr.
- apply wdgr ; [ apply wdgll | apply wdglr ] ; (eapply H ; [ | reflexivity ]) ; simpl ; lia.
- apply frlr.
  simpl ; apply (frll (cdvar 0)) ; auto.
  eapply H ; [ | reflexivity ].
  rewrite fsize_subs_cdvar ; rewrite fsize_fup ; simpl ; lia.
Qed.



