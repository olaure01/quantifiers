(* Definitions and properties of first-order terms *)
(*   with holes in [nat] for de Bruijn indices *)

(* arity check based on vectors *)

Require Export PeanoNat.
Require Import Vector_more.
Notation vec := Vector.t.
Require List.

Create HintDb term_db.

Tactic Notation "rnow" tactic(T) :=
  T ; simpl ; autorewrite with term_db in * ; simpl ; intuition.
Tactic Notation "rnow" tactic(T) "then" tactic(T1) :=
  T ; simpl ; autorewrite with term_db in * ; simpl ; intuition T1 ; simpl ; intuition.

Lemma ltb_S : forall n m, (S n <? S m) = (n <? m).
Proof. reflexivity. Qed.
Hint Rewrite ltb_S : term_db.


(** * Different kinds of atoms *)

Parameter tatom : Type. (* function symbols for [term] *)
Parameter tarity : tatom -> nat. (* arity of function symbols *)
Parameter vatom : Type. (* variables for quantification *)
Parameter beq_vat : vatom -> vatom -> bool. (* boolean equality on [vatom] *)
Parameter beq_eq_vat : forall a b, beq_vat a b = true <-> a = b.
   (* equality specification for [vatom] *)

(* [vatom] presented as a type with Boolean equality *)
Module vatomBoolEq <: Equalities.UsualBoolEq.
Definition t := vatom.
Definition eq := @eq vatom.
Definition eqb := beq_vat.
Definition eqb_eq := beq_eq_vat.
End vatomBoolEq.
Module vatomEq := Equalities.Make_UDTF vatomBoolEq.
Module vatomFacts := Equalities.BoolEqualityFacts vatomEq.
Export vatomFacts.

Ltac case_analysis :=
match goal with
| |- context f [?x =? ?y] => case_eq (x =? y)
| |- context f [?x <? ?y] => case_eq (x <? y)
| |- context f [?x ?= ?y] => case_eq (x ?= y)
| |- context f [beq_vat ?x ?y] => case_eq (beq_vat x y)
| |- context f [vatomEq.eq_dec ?x  ?y] => case_eq (vatomEq.eq_dec x y)
end.
Ltac rcauto := simpl ; autorewrite with term_db in * ; simpl ; rnow case_analysis.



(** * First-Order Terms *)

(** terms with quantifiable variables *)
(** [dvar] for De Bruijn style eigen variables in proofs *)
(** [tvar] for quantified variables in formulas *)
Inductive term :=
| dvar : nat -> term
| tvar : vatom -> term
| tconstr : forall f, vec term (tarity f) -> term.

(** appropriate induction for [term] (with list inside): so called "nested fix" *)
Fixpoint term_ind_vec_Forall u :
  forall P : _ -> Prop,
  (forall n, P (dvar n)) ->
  (forall x, P (tvar x)) ->
  (forall f l, Forall P l -> P (tconstr f l)) -> P u :=
fun P Pdvar Ptvar Pconstr =>
match u with
| dvar n => Pdvar n
| tvar x => Ptvar x
| tconstr c l => Pconstr c l
    ((fix l_ind k l' : Forall P l' :=
      match l' with
      | nil _ => Forall_nil P
      | cons _ t1 k l1 => Forall_cons _ _ _
                          (term_ind_vec_Forall t1 P Pdvar Ptvar Pconstr)
                          (l_ind k l1)
      end) (tarity c) l)
end.
Ltac term_induction u :=
  (try intros until u) ;
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  apply (term_ind_vec_Forall u) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ;
    repeat (rewrite List.flat_map_concat_map) ; repeat (rewrite map_map) ;
    try f_equal ; try (apply map_ext_in ; apply Forall_forall) ; try assumption ] ;
  try ((rnow idtac) ; fail) ; try (rcauto ; fail).


(** lift indexes above [k] in [term] [v] *)
Fixpoint tup k v :=
match v with
| dvar n => if n <? k then dvar n else dvar (S n)
| tvar x => tvar x
| tconstr f l => tconstr f (map (tup k) l)
end.

Lemma tup_tup_com : forall k u,
  tup (S k) (tup 0 u) = tup 0 (tup k u).
Proof. term_induction u. Qed.
Hint Rewrite tup_tup_com : term_db.

(** * Term substitutions *)

(** substitutes [term] [u] for index [n] in [term] [v] and decreases indexes above [n] *)
Fixpoint ntsubs n u v :=
match v with
| tvar x => tvar x
| dvar k => match n ?= k with
            | Eq => u
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| tconstr f l => tconstr f (map (ntsubs n u) l)
end.

(** substitutes [term] [u] for variable [x] in [term] [v] *)
Fixpoint tsubs x u v :=
match v with
| tvar y => if (beq_vat y x) then u else tvar y
| dvar k => dvar k
| tconstr c l => tconstr c (map (tsubs x u) l)
end.

Lemma tup_tsubs_com : forall k x u v,
  tup k (tsubs x u v) = tsubs x (tup k u) (tup k v).
Proof. term_induction v. Qed.
Hint Rewrite tup_tsubs_com : term_db.

Lemma ntsubs_tup_com : forall k u v,
  ntsubs (S k) (tup 0 u) (tup 0 v) = tup 0 (ntsubs k u v).
Proof. term_induction v ; rcauto.
now destruct n ; destruct k ; inversion H.
Qed.
Hint Rewrite ntsubs_tup_com : term_db.

Lemma ntsubs_z_tup : forall u v, ntsubs 0 u (tup 0 v) = v.
Proof. term_induction v.
now rewrite <- (map_id l) at 2 ; apply map_ext_in ; apply Forall_forall.
Qed.
Hint Rewrite ntsubs_z_tup : term_db.



(** ** Free variables *)

Fixpoint freevars u :=
match u with
| tvar x => List.cons x List.nil
| dvar _ => List.nil
| tconstr f l => fold_right (fun x => app (freevars x)) l List.nil
end.
Notation closed u := (freevars u = List.nil).

Lemma closed_nofreevars : forall u x, closed u -> ~ List.In x (freevars u).
Proof. intros ? ? Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve closed_nofreevars : term_db.

Lemma freevars_tup : forall k u, freevars (tup k u) = freevars u.
Proof.
intros until u ;
apply (term_ind_vec_Forall u) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ] ;
  try ((rnow idtac) ; fail) ; try (rcauto ; fail).
revert IHll; induction ll ; intros IHl ; intuition.
inversion IHl ; subst.
apply inj_pairT2_nat in H1 ; subst.
apply IHll in H3.
simpl ; rewrite H3 ; rewrite H2 ; reflexivity.
Qed.
Hint Rewrite freevars_tup : term_db.

Lemma freevars_ntsubs : forall n u, closed u -> forall v,
  freevars (ntsubs n u v) = freevars v.
Proof.
intros until v ;
apply (term_ind_vec_Forall v) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ] ;
  try ((rnow idtac) ; fail) ; try (rcauto ; fail).
revert IHll; induction ll ; intros IHl ; intuition.
inversion IHl ; subst.
apply inj_pairT2_nat in H2 ; subst.
apply IHll in H4.
simpl ; rewrite H4 ; rewrite H3 ; reflexivity.
Qed.
Hint Rewrite freevars_ntsubs using intuition ; fail : term_db.

Lemma nfree_tsubs : forall x u v, ~ List.In x (freevars v) -> tsubs x u v = v.
Proof. term_induction v ; try rcauto.
- now apply vatomEq.eqb_eq in H.
- rnow intros Heq ; f_equal ; revert IHl Heq ; induction l ; intros.
  rnow inversion IHl0 ; apply inj_pairT2_nat in H1 ; subst ;
       rewrite H2 ; [ f_equal | ] ; simpl in Heq.
Qed.
Hint Rewrite nfree_tsubs using try (intuition ; fail) ;
                               (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma ntsubs_tsubs_com : forall x v n u, ~ List.In x (freevars u) -> forall w,
  ntsubs n u (tsubs x v w) = tsubs x (ntsubs n u v) (ntsubs n u w).
Proof. term_induction w. Qed.
Hint Rewrite ntsubs_tsubs_com using try (intuition ; fail) ;
                                    (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma tsubs_tsubs_com : forall x v y u, beq_vat x y = false -> ~ List.In x (freevars u) ->
  forall w, tsubs y u (tsubs x v w) = tsubs x (tsubs y u v) (tsubs y u w).
Proof. term_induction w.
rnow case_eq (beq_vat x0 x) ; case_eq (beq_vat x0 y) then try rewrite H1 ; try rewrite H2.
exfalso.
now rewrite eqb_neq in H ; rewrite beq_eq_vat in H1 ; rewrite beq_eq_vat in H2 ; subst.
Qed.
Hint Rewrite tsubs_tsubs_com using try (intuition ; fail) ;
                                   (try apply closed_nofreevars) ; intuition ; fail : term_db.

