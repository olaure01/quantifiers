(* Definitions and properties of first-order terms *)
(*   with holes in [nat] for de Bruijn indices *)

(* with arity checks *)


Require Export PeanoNat List.
Require Import dectype term_tactics.


(** * Different kinds of atoms *)

Parameter tatom : Type. (* function symbols for [term] *)
Parameter tarity : tatom -> nat. (* arity of function symbols *)
Parameter vatom : DecType. (* variables for quantification *)


(** * First-Order Terms *)

(** terms with quantifiable variables *)
(** [nat] value gives number of missing arguments to get appropriate arity *)
(** [dvar] for De Bruijn style eigen variables in proofs *)
(** [tvar] for quantified variables in formulas *)
Inductive term : nat -> Type :=
| dvar : nat -> term 0
| tvar : vatom -> term 0
| tfun : forall f, term (tarity f)
| tconstr : forall (t : term 0) {k}, term (S k) -> term k.

(*
Inductive tForall P : forall k, term k -> Prop :=
| Fdvar : forall n, P (dvar n) -> tForall P _ (dvar n)
| Ftvar : forall x, P (tvar x) -> tForall P _ (tvar x)
| Ftfun : forall f, tForall P _ (tfun f)
| Ftconstr : forall t k p, P t -> tForall P _ p -> tForall P _ (tconstr t k p).

Goal forall P t, tForall P 0 t.
induction t ; constructor.
*)

Ltac simpl_term_induction v :=
  induction v ; try rcauto ; try reflexivity ;
    try (simpl ; f_equal ; assumption).

(** lift indexes above [k] in [term] [v] *)
Fixpoint tup k {m} (v : term m) :=
match v with
| dvar n => if n <? k then dvar n else dvar (S n)
| tvar x => tvar x
| tfun f => tfun f
| tconstr t p => tconstr (tup k t) (tup k p)
end.

Lemma tup_tup_com : forall k {m} (u : term m),
  tup (S k) (tup 0 u) = tup 0 (tup k u).
Proof. simpl_term_induction u. Qed.
Hint Rewrite tup_tup_com : term_db.

(** * Term substitutions *)

(** substitutes [term] [u] for index [n] in [term] [v] and decreases indexes above [n] *)
Fixpoint ntsubs n u {m} (v : term m) :=
match v with
| tvar x => tvar x
| dvar k => match n ?= k with
            | Eq => u
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| tfun f => tfun f
| tconstr t p => tconstr (ntsubs n u t) (ntsubs n u p)
end.

(** substitutes [term] [u] for variable [x] in [term] [v] *)
Fixpoint tsubs x u {m} (v : term m) :=
match v with
| tvar y => if (eqb y x) then u else tvar y
| dvar k => dvar k
| tfun f => tfun f
| tconstr t p => tconstr (tsubs x u t) (tsubs x u p)
end.

Lemma tup_tsubs_com : forall k x u {m} (v : term m),
  tup k (tsubs x u v) = tsubs x (tup k u) (tup k v).
Proof. simpl_term_induction v. Qed.
Hint Rewrite tup_tsubs_com : term_db.

Lemma ntsubs_tup_com : forall k u {m} (v : term m),
  ntsubs (S k) (tup 0 u) (tup 0 v) = tup 0 (ntsubs k u v).
Proof. simpl_term_induction v; now destruct n ; destruct k ; inversion Heq. Qed.
Hint Rewrite ntsubs_tup_com : term_db.

Lemma ntsubs_z_tup : forall u {m} (v : term m), ntsubs 0 u (tup 0 v) = v.
Proof. simpl_term_induction v. Qed.
Hint Rewrite ntsubs_z_tup : term_db.



(** ** Free variables *)

Fixpoint freevars {m} (u : term m) :=
match u with
| tvar x => cons x nil
| dvar _ => nil
| tfun _ => nil
| tconstr t p => app (freevars t) (freevars p)
end.
Notation closed u := (freevars u = nil).

Lemma closed_nofreevars : forall {m} (u : term m) x, closed u -> ~ In x (freevars u).
Proof. intros ? ? ? Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve closed_nofreevars : term_db.

Lemma freevars_tup : forall k {m} (u : term m), freevars (tup k u) = freevars u.
Proof. simpl_term_induction u. Qed.
Hint Rewrite freevars_tup : term_db.

Lemma freevars_ntsubs : forall n u, closed u -> forall {m'} (v : term m'),
  freevars (ntsubs n u v) = freevars v.
Proof. simpl_term_induction v. Qed.
Hint Rewrite freevars_ntsubs using intuition ; fail : term_db.

Lemma nfree_tsubs : forall x u {m} (v :term m), ~ In x (freevars v) -> tsubs x u v = v.
Proof. simpl_term_induction v. Qed.
Hint Rewrite nfree_tsubs using try (intuition ; fail) ;
                               (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma ntsubs_tsubs_com : forall x v n u, ~ In x (freevars u) -> forall {m} (w : term m),
  ntsubs n u (tsubs x v w) = tsubs x (ntsubs n u v) (ntsubs n u w).
Proof. simpl_term_induction w. Qed.
Hint Rewrite ntsubs_tsubs_com using try (intuition ; fail) ;
                                    (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma tsubs_tsubs_com : forall x v y u, x <> y -> ~ In x (freevars u) ->
  forall {m} (w : term m), tsubs y u (tsubs x v w) = tsubs x (tsubs y u v) (tsubs y u w).
Proof. simpl_term_induction w. Qed.
(*
Hint Rewrite tsubs_tsubs_com using try (intuition ; fail) ;
                                   (try apply closed_nofreevars) ; intuition ; fail : term_db.
*)

