(* Definitions and properties of first-order terms *)
(*   with holes in [nat] for de Bruijn indices *)

Require Export PeanoNat.
Require Export List.

Tactic Notation "rnow" tactic(t) :=
  t ; simpl ; autorewrite with core in * ; simpl ; intuition.
Tactic Notation "rnow" tactic(t) "then" tactic(t1) :=
  t ; simpl ; autorewrite with core in * ; simpl ; intuition t1 ; simpl ; intuition.

Lemma ltb_S : forall n m, (S n <? S m) = (n <? m).
Proof. reflexivity. Qed.
Hint Rewrite ltb_S.


(** * Different kinds of atoms *)

Parameter tatom : Type. (* function symbols for [term] *)
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
Ltac rcauto := simpl ; autorewrite with core in * ; simpl ; rnow case_analysis.



(** * First-Order Terms *)

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
(** [dvar] for De Bruijn style eigen variables in proofs *)
(** [tvar] for quantified variables in formulas *)
Inductive term :=
| dvar : nat -> term
| tvar : vatom -> term
| tconstr : tatom -> list term -> term.

(** appropriate induction for [term] (with list inside): so called "nested fix" *)
Fixpoint term_ind_list_Forall t :
  forall P : term -> Prop,
  (forall n, P (dvar n)) ->
  (forall x, P (tvar x)) ->
  (forall f l, Forall P l -> P (tconstr f l)) -> P t :=
fun P Pdvar Ptvar Pconstr =>
match t with
| dvar n => Pdvar n
| tvar x => Ptvar x
| tconstr c l => Pconstr c l
    ((fix l_ind l' : Forall P l' :=
      match l' with
      | nil => Forall_nil P
      | cons t1 l1 => Forall_cons _
                        (term_ind_list_Forall t1 P Pdvar Ptvar Pconstr)
                        (l_ind l1)
      end) l)
end.
Ltac term_induction t :=
  (try intros until t) ;
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  apply (term_ind_list_Forall t) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ;
    repeat (rewrite flat_map_concat_map) ; repeat (rewrite map_map) ;
    try f_equal ; try (apply map_ext_in ; apply Forall_forall) ; try assumption ] ;
  try ((rnow idtac) ; fail) ; try (rcauto ; fail).


(** lift indexes above [k] in [term] [t] *)
Fixpoint tup k t :=
match t with
| dvar n => if n <? k then dvar n else dvar (S n)
| tvar x => tvar x
| tconstr f l => tconstr f (map (tup k) l)
end.

Lemma tup_tup_com : forall k t,
  tup (S k) (tup 0 t) = tup 0 (tup k t).
Proof. term_induction t. Qed.
Hint Rewrite tup_tup_com.

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

(** substitutes [term] [u] for variable [x] in [term] [t] *)
Fixpoint tsubs x u t :=
match t with
| tvar y => if (beq_vat y x) then u else tvar y
| dvar k => dvar k
| tconstr c l => tconstr c (map (tsubs x u) l)
end.

Lemma tup_tsubs_com : forall k x u t,
  tup k (tsubs x u t) = tsubs x (tup k u) (tup k t).
Proof. term_induction t. Qed.
Hint Rewrite tup_tsubs_com.

Lemma ntsubs_tup_com : forall k u t,
  ntsubs (S k) (tup 0 u) (tup 0 t) = tup 0 (ntsubs k u t).
Proof. term_induction t ; rcauto.
now destruct n ; destruct k ; inversion H.
Qed.
Hint Rewrite ntsubs_tup_com.

Lemma ntsubs_z_tup : forall u t, ntsubs 0 u (tup 0 t) = t.
Proof. term_induction t.
now rewrite <- (map_id l) at 2 ; apply map_ext_in ; apply Forall_forall.
Qed.
Hint Rewrite ntsubs_z_tup.



(** ** Free variables *)

Fixpoint freevars t :=
match t with
| tvar x => x :: nil
| dvar _ => nil
| tconstr f l => flat_map freevars l
end.
Notation closed t := (freevars t = nil).

Lemma closed_nofreevars : forall t x, closed t -> ~ In x (freevars t).
Proof. intros t x Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve closed_nofreevars.

Lemma freevars_tup : forall k t, freevars (tup k t) = freevars t.
Proof. term_induction t. Qed.
Hint Rewrite freevars_tup.

Lemma freevars_ntsubs : forall n u, closed u -> forall t,
  freevars (ntsubs n u t) = freevars t.
Proof. term_induction t. Qed.
Hint Rewrite freevars_ntsubs using intuition ; fail.

Lemma nfree_tsubs : forall x u t, ~ In x (freevars t) -> tsubs x u t = t.
Proof. term_induction t ; try rcauto.
- now apply vatomEq.eqb_eq in H.
- rnow intros Heq ; f_equal ; revert IHl Heq ; induction l ; intros.
  rnow inversion IHl0 ; subst ; rewrite H1 ; [ f_equal | ] ; simpl in Heq.
Qed.
Hint Rewrite nfree_tsubs using try (intuition ; fail) ;
                               (try apply closed_nofreevars) ; intuition ; fail.

Lemma ntsubs_tsubs_com : forall x v n u, ~ In x (freevars u) -> forall t,
  ntsubs n u (tsubs x v t) = tsubs x (ntsubs n u v) (ntsubs n u t).
Proof. term_induction t. Qed.
Hint Rewrite ntsubs_tsubs_com using try (intuition ; fail) ;
                                    (try apply closed_nofreevars) ; intuition ; fail.

Lemma tsubs_tsubs_com : forall x v y u, beq_vat x y = false -> ~ In x (freevars u) -> forall t,
  tsubs y u (tsubs x v t) = tsubs x (tsubs y u v) (tsubs y u t).
Proof. term_induction t.
rnow case_eq (beq_vat x0 x) ; case_eq (beq_vat x0 y) then try rewrite H1 ; try rewrite H2.
exfalso.
now rewrite eqb_neq in H ; rewrite beq_eq_vat in H1 ; rewrite beq_eq_vat in H2 ; subst.
Qed.
Hint Rewrite tsubs_tsubs_com using try (intuition ; fail) ;
                                   (try apply closed_nofreevars) ; intuition ; fail.


