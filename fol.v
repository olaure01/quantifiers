(* Coq 8.7.1 *)

Require Import PeanoNat.
Require Import EqNat.
Require Import Omega.
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
case_eq (n <? k) ; intros Heq ; rewrite <- ltb_S ; rewrite Heq ; auto.
Qed.

(** substitutes index [k] for variable [x] in [term] [t] *)
Fixpoint tmkn k x t :=
match t with
| dvar n => dvar n
| tvar y => if (beq_vat x y) then dvar k else tvar y
| tconstr c l => tconstr c (map (tmkn k x) l)
end.

Lemma tup_tmkn_tup : forall k x t,
  tup (S k) (tmkn 0 x (tup 0 t)) = tmkn 0 x (tup 0 (tup k t)).
Proof.
intros ; term_induction t.
- case_eq (n <? k) ; intros Heq ; rewrite <- ltb_S ; rewrite Heq ; auto.
- case_eq (beq_vat x x0) ; auto.
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

Hint Resolve cup_tup.

Lemma tmkn_cterm : forall k x u,
  tmkn k x (cterm_to_term u) = cterm_to_term u.
Proof.
intros ; cterm_induction u.
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

Hint Resolve tsubs_cterm.

Lemma tup_tsubs_com : forall k x u t,
  tup k (tsubs x u t) = tsubs x (cup k u) (tup k t).
Proof.
intros ; term_induction t.
- case_eq (n <? k) ; auto.
- case_eq (beq_vat x0 x) ; auto.
Qed.

Lemma tsubs_tsubs_com : forall x v y u t, beq_vat x y = false ->
  tsubs y u (tsubs x v t) = tsubs x v (tsubs y u t).
Proof.
intros ; term_induction t.
case_eq (beq_vat x0 x) ; case_eq (beq_vat x0 y) ; intros Heq1 Heq2 ; simpl ;
  try now (try rewrite Heq1 ; try rewrite Heq2 ; auto).
exfalso.
apply vatomEq.eqb_eq in Heq1 ; apply vatomEq.eqb_eq in Heq2 ; subst.
rewrite eqb_refl in H ; inversion H.
Qed.

Lemma tsubs_cdvar_tmkn : forall k x t, tsubs x (cdvar k) t = tmkn k x t.
Proof.
intros ; term_induction t.
rewrite eqb_sym ; case_eq (beq_vat x0 x) ; auto.
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

Hint Resolve tup_tup_com tup_tmkn_tup tmkn_cterm
 tup_tsubs_com tsubs_tsubs_com tsubs_cdvar_tmkn ntsubs_cterm.

Lemma ntsubs_tup_com : forall k n u t,
  ntsubs (S (k + n)) (cup k u) (tup k t) = tup k (ntsubs (k + n) u t).
Proof.
intros ; term_induction t.
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

Lemma ntsubs_tmkn_com : forall x n u t,
  ntsubs (S n) u (tmkn 0 x t) = tmkn 0 x (ntsubs (S n) u t).
Proof.
intros ; term_induction t.
- destruct n0 ; simpl.
  + reflexivity.
  + case_eq (n ?= n0) ; auto.
- case_eq (beq_vat x x0) ; auto.
Qed.

Lemma ntsubs_tsubs_com : forall x v n u t,
  ntsubs n u (tsubs x v t) = tsubs x (ncsubs n u v) (ntsubs n u t).
Proof.
intros ; term_induction t.
- case_eq (n ?= n0) ; auto.
- case_eq (beq_vat x0 x) ; auto.
Qed.

Hint Resolve ntsubs_tup_com ntsubs_tmkn_com ntsubs_tsubs_com.



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
  [ try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; auto ;
                       rewrite IHll ; f_equal ; auto)
  | auto
  | try (f_equal ; auto)
  | try (f_equal ; auto) ].


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
Proof.
intros ; formula_induction A.
Qed.

Hint Resolve fup_fup_com.

(** substitutes index [k] for variable [x] in [formula] [A] *)
Fixpoint mkn k x A :=
match A with
| var X l => var X (map (tmkn k x) l)
| top => top
| wdg B C => wdg (mkn k x B) (mkn k x C)
| frl y B as C => if (beq_vat y x) then C else frl y (mkn k x B)
end.

Lemma fup_mkn_fup : forall k x A,
  fup (S k) (mkn 0 x (fup 0 A)) = mkn 0 x (fup 0 (fup k A)).
Proof.
intros ; formula_induction A.
case_eq (beq_vat x0 x) ; intros Heq ; simpl ; f_equal ; auto.
Qed.

(** substitutes [cterm] [u] for variable [x] in [formula] [A] *)
Fixpoint subs x u A :=
match A with
| var X l => var X (map (tsubs x u) l)
| top => top
| wdg B C => wdg (subs x u B) (subs x u C)
| frl y B as C => if (beq_vat y x) then C else frl y (subs x u B)
end.

Lemma subs_subs_com : forall x v y u A, beq_vat x y = false ->
  subs y u (subs x v A) = subs x v (subs y u A).
Proof.
intros x v y u A ; formula_induction A ; intros Hneq ; try now (f_equal ; auto).
- f_equal.
  induction l ; auto ; now (simpl ; f_equal ; auto).
- case_eq (beq_vat x0 x) ; intros Heq1 ; simpl ; case_eq (beq_vat x0 y) ; intros Heq2 ; 
    simpl ; try rewrite Heq1 ; simpl ; f_equal ; auto.
Qed.

Lemma subs_cdvar_mkn : forall k x A, subs x (cdvar k) A = mkn k x A.
Proof.
intros ; formula_induction A.
case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal ; auto.
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

Lemma nsubs_fup_com : forall k n u A,
  nsubs (S (k + n)) (cup k u) (fup k A) = fup k (nsubs (k + n) u A).
Proof.
intros ; formula_induction A.
Qed.

Lemma nsubs_mkn_com : forall x n u A,
  nsubs (S n) u (mkn 0 x A) = mkn 0 x (nsubs (S n) u A).
Proof.
intros ; formula_induction A.
case_eq (beq_vat x0 x) ; intros Heq ; simpl ; f_equal ; auto.
Qed.

Lemma nsubs_subs_com : forall x v n u A,
  nsubs n u (subs x v A) = subs x (ncsubs n u v) (nsubs n u A).
Proof.
intros ; formula_induction A.
case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal ; auto.
Qed.

Hint Resolve fup_mkn_fup nsubs_fup_com nsubs_mkn_com nsubs_subs_com.

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
  ntsubs 0 u (tmkn 0 x (tup 0 t)) = tsubs x u t.
Proof.
intros ; term_induction t.
rewrite eqb_sym ; case_eq (beq_vat x0 x) ; simpl ; auto.
Qed.

Hint Resolve nsubs_z_fup ntsubs_z_tsubs_tup.

Lemma nsubs_z_subs_fup : forall u x A,
  nsubs 0 u (mkn 0 x (fup 0 A)) = subs x u A.
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
| frlr { x C A } : prove (fup 0 C) (mkn 0 x (fup 0 A)) -> prove C (frl x A)
| frll { x A C } : forall u, prove (subs x u A) C -> prove (frl x A) C.


(** substitutes [cterm] [u] for index [n] in proof [pi] and decreases indexes above [n] *)
Fixpoint psubs n u {C A} (pi : prove C A) : prove (nsubs n u C) (nsubs n u A).
Proof.
destruct pi.
- apply ax.
- apply topr.
- simpl ; apply wdgr ; apply psubs ; assumption.
- simpl ; apply wdgll ; apply psubs ; assumption.
- simpl ; apply wdglr ; apply psubs ; assumption.
- simpl ; apply frlr.
  change n with (0 + n).
  rewrite <- nsubs_fup_com ; simpl.
  change n with (0 + n).
  rewrite <- nsubs_fup_com ; simpl.
  rewrite <- nsubs_mkn_com.
  apply psubs ; assumption.
- simpl ; apply (frll (ncsubs n u u0)).
  rewrite <- nsubs_subs_com.
  apply psubs ; assumption.
Defined.

(** lift indexes above [k] in proof [pi] *)
Fixpoint pup k {C A} (pi : prove C A) : prove (fup k C) (fup k A) :=
match pi with
| ax _ => ax (fup k _)
| topr _ => topr _
| wdgr pi1 pi2 => wdgr (pup k pi1) (pup k pi2)
| wdgll _ pi1 => wdgll _ (pup k pi1)
| wdglr _ pi1 => wdglr _ (pup k pi1)
| frlr pi1 => frlr (eq_rec _ (fun X => prove X _)
                             (eq_rec _ (fun X => prove _ X)
                                       (pup (S k) pi1) _
                                       (fup_mkn_fup _ _ _)) _
                             (fup_fup_com _ _))
| frll _ pi1 => frll _ (eq_rec _ (fun X => prove X _)
                                 (pup k pi1) _
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
| frll _ pi1 => S (psize pi1)
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

Lemma psize_psubs : forall k u {A B} (pi : prove A B),
  psize (psubs k u pi) = psize pi.
Proof.
intros k u A B pi.
revert k u ; induction pi ; intros k u' ; simpl ; auto.
- f_equal.
  rewrite psize_eq_recl.
  rewrite psize_eq_recr_P.
  rewrite psize_eq_recr.
  apply IHpi.
- f_equal.
  rewrite psize_eq_recl.
  apply IHpi.
Qed.

Lemma psize_pup : forall k {A B} (pi : prove A B),
  psize (pup k pi) = psize pi.
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
  (* dependent induction pi1. *)
  + apply wdgll ; assumption.
  + apply (IH _ _ _ pi1_1 pi2) ; simpl ; lia.
  + apply wdgll.
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
  + apply (frll u).
    apply (IH _ _ _ pi1 (wdgll _ pi2)) ; simpl ; lia.
- cut (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (wdglr B pi2) -> prove A1 C0),
         D = wdg B A0 -> prove A C) ; [ | clear ].
  { intros IH2 ; eapply IH2 ; [ eassumption | reflexivity ]. }
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  (* dependent induction pi1. *)
  + apply wdglr ; assumption.
  + apply (IH _ _ _ pi1_2 pi2) ; simpl ; lia.
  + apply wdgll.
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
  + apply (frll u).
    apply (IH _ _ _ pi1 (wdglr _ pi2)) ; simpl ; lia.
- apply frlr.
  apply (IH _ _ _ (pup 0 pi1) pi2).
  rewrite psize_pup ; simpl ; lia.
- cut (forall A D (pi1 : prove A D) x A0 C u (pi2 : prove (subs x u A0) C)
              (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (frll u pi2) -> prove A1 C0),
         D = frl x A0 -> prove A C) ; [ | clear ].
  { intros IH2 ; eapply IH2 ; [ eassumption | reflexivity ]. }
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst.
  (* dependent induction pi1. *)
  + apply (frll u) ; assumption.
  + apply wdgll.
    apply (IH _ _ _ pi1 (frll _ pi2)) ; simpl ; lia.
  + apply wdglr.
    apply (IH _ _ _ pi1 (frll _ pi2)) ; simpl ; lia.
  + remember (eq_rec _ (fun X => prove X _)
                       (eq_rec _ (fun X => prove _ X)
                                 (psubs 0 u pi1) _
                                 (nsubs_z_subs_fup _ _ _)) _
                       (nsubs_z_fup _ _)) as pi1'.
    apply (IH _ _ _ pi1' pi2).
    rewrite Heqpi1'.
    rewrite psize_eq_recl.
    rewrite psize_eq_recr.
    rewrite psize_psubs.
    simpl ; lia.
 + apply (frll u).
   apply (IH _ _ _ pi1 (frll _ pi2)) ; simpl ; lia.
Qed.



(** * Free variables *)
Inductive tfree x : term -> Prop :=
| tf_var : tfree x (tvar x)
| tf_constr : forall c l, Exists (tfree x) l -> tfree x (tconstr c l).

Inductive free x : formula -> Prop :=
| f_var : forall X l, Exists (tfree x) l -> free x (var X l)
| f_wdgl : forall A B, free x A -> free x (wdg A B)
| f_wdgr : forall A B, free x A -> free x (wdg B A)
| f_frl : forall y A, beq_vat y x = false -> free x A -> free x (frl y A).

Lemma nfree_tmkn : forall k x t, ~ tfree x t -> tmkn k x t = t.
Proof.
intros k x t ; revert x ; term_induction t ; intros y Hnf.
- case_eq (beq_vat y x) ; intros ; auto.
  apply vatomEq.eqb_eq in H ; subst.
  contradiction Hnf ; constructor.
- f_equal.
  revert IHl Hnf ; induction l ; intros HF Hnf ; auto.
  inversion HF ; subst ; simpl ; f_equal.
  + apply H1.
    intros Hf ; apply Hnf.
    now (constructor ; constructor ; assumption).
  + apply IHl ; auto.
    intros Hf ; inversion Hf ; subst ; apply Hnf.
    now (constructor ; constructor ; assumption).
Qed.

Lemma nfree_mkn : forall k x A, ~ free x A -> mkn k x A = A.
Proof.
intros ; formula_induction A.
- apply nfree_tmkn.
  intros Hf ; apply H ; now (constructor ; constructor ; assumption).
- intros Hf.
  inversion Hf ; subst.
  apply H ; now (constructor ; constructor ; assumption).
- apply A1.
  intros Hf ; apply H ; now (constructor ; assumption).
- apply IHA1.
  intros Hf ; apply H ; now (constructor ; assumption).
- case_eq (beq_vat x0 x) ; intros Heq ; auto.
  f_equal.
  apply IHA ; intros Hf ; apply H ; constructor ; auto.
Qed.

Lemma tfree_tup : forall k x t, tfree x (tup k t) -> tfree x t.
Proof.
intros k x t ; revert x ; term_induction t ; intros y Hf ; auto.
- revert Hf ; case_eq (n <? k) ; intros Heq Hf ; inversion Hf.
- inversion Hf ; subst ; clear Hf ; constructor.
  revert IHl H0 ; induction l ; intros HF Hf ; auto.
  inversion HF ; inversion Hf ; subst ; now (constructor ; auto).
Qed.

Lemma free_fup : forall k x A, free x (fup k A) -> free x A.
Proof.
intros ; formula_induction A ; inversion H ; subst ;
  try (now constructor ; auto).
inversion H ; subst ; constructor.
revert H1 ; clear H ; induction l ; intros Ht ; inversion Ht ; subst.
- apply Exists_cons_hd ; apply (tfree_tup k) ; assumption.
- now (constructor ; auto).
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
  rewrite subs_cdvar_mkn.
  apply ax.
- apply frlr ; simpl.
  apply (frll (cdvar 0)) ; simpl.
  apply wdglr.
  rewrite subs_cdvar_mkn.
  apply ax.
Qed.

Lemma frl_nfree : forall A x, ~ free x A -> prove A (frl x A).
Proof.
intros A x Hnf.
apply frlr.
rewrite nfree_mkn.
- apply ax.
- intros Hf ; apply Hnf.
  apply (free_fup 0) ; assumption.
Qed.



