(* Definitions and Properties of First-Order Terms *)
(*   with holes in [nat] for de Bruijn indices *)

(* with arity checks *)

From Coq Require Export PeanoNat List.
From OLlibs Require Import List_more.
From OLlibs Require Export dectype.

Require Export term_tactics.

Set Implicit Arguments.

(* Extensional equality of functions *)
Infix "==" := (fun f g => forall x, f x = g x) (at level 70).


(** * First-Order Terms *)

Section Terms.

Context { vatom : DecType } { tatom : Type }.
Context { tarity : tatom -> nat }. (* arity of function symbols *)

(** terms with quantifiable variables

 - [evar] for De Bruijn style eigen variables in proofs,
             type for these indices as parameter called the eigen type,
             but mostly used with [nat].
             Other values can be used (for terms without indices, use [Empty_set]).
 - [tvar] for quantified variables in formulas *)
Inductive term T : nat -> Type :=
| evar : T -> term T 0
| tvar : vatom -> term T 0
| tfun : forall f, term T (tarity f)
| tconstr : forall (t : term T 0) {k}, term T (S k) -> term T k.
Arguments evar {T}.
Arguments tfun {T}.

Ltac term_induction t :=
  try (intros until t); (* to avoid name clashes in induction t *)
  let nn := fresh "n" in
  let xx := fresh "x" in
  let ff := fresh "f" in
  let kk := fresh "k" in
  let uu := fresh "u" in
  let ll := fresh "l" in
  let IHuu := fresh "IHu" in
  let IHll := fresh "IHl" in
  induction t as [nn | xx | ff | uu IHuu kk ll IHll]; try (now intuition); simpl; intros;
  try (apply (f_equal2 (fun x y => tconstr x y)); try (now intuition));
  try (now rcauto);
  try (now f_equal; rcauto).


(** * Monad structure on [term] via substitution *)

(** substitutes the [term] [r n] for index [n] in [term] [t] *)
Fixpoint tesubs T1 T2 k (r : T1 -> term T2 0) (t : term T1 k) :=
match t with
| tvar _ x => tvar T2 x
| evar k => r k
| tfun f => tfun f
| tconstr u v => tconstr (tesubs r u) (tesubs r v)
end.
Notation "t ⟦ r ⟧" := (tesubs r t) (at level 8, left associativity, format "t ⟦ r ⟧").

(** monad structure induced on [term] *)
Lemma evar_tesubs T1 T2 (r : T1 -> term T2 0) :
  forall x, (evar x)⟦r⟧ = r x.
Proof. reflexivity. Qed.
Hint Rewrite evar_tesubs : term_db.

Lemma tesubs_evar T k : forall (t : term T k),
  t⟦evar⟧ = t.
Proof. term_induction t. Qed.
Hint Rewrite tesubs_evar : term_db.

Definition fecomp T1 T2 T3 (r : T1 -> term T2 0) (s : T2 -> term T3 0) := fun x => (r x)⟦s⟧.
Notation "r ;; s" := (fecomp r s) (at level 20, format "r  ;;  s").

Lemma tesubs_comp T1 T2 T3 k (r : T1 -> term T2 0) (s : T2 -> term T3 0) :
  forall t : term T1 k, t⟦r⟧⟦s⟧ = t⟦r ;; s⟧.
Proof. term_induction t. Qed.
Hint Rewrite tesubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma tesubs_ext T1 T2 k (r1 r2 : T1 -> term T2 0) :
  r1 == r2 -> forall t : term T1 k, t⟦r1⟧ = t⟦r2⟧.
Proof. term_induction t. Qed.
Hint Resolve tesubs_ext : term_db.
(* TODO could be turned into a morphism *)


Section Fixed_Eigen_Type.

Variable T : Type.
Implicit Type t : term T 0.
Arguments tvar {T} _.

(** * Term substitution *)

(** substitutes [term] [u] for variable [x] in [term] [t] *)
Fixpoint tsubs k x u (t : term T k) :=
match t with
| tvar y => if (eqb y x) then u else tvar y
| evar k => evar k
| tfun f => tfun f
| tconstr v l => tconstr (tsubs x u v) (tsubs x u l)
end.
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").

Lemma tsubs_tsubs_eq : forall x u v t, t[v//x][u//x] = t[v[u//x]//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tsubs_eq : term_db.


(** * Variables *)

Fixpoint tvars k (t : term T k) :=
match t with
| tvar x => x :: nil
| evar _ => nil
| tfun _ => nil
| tconstr v l => tvars l ++ tvars v
end.
Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation "x ∉ t" := (~ In x (tvars t)) (at level 30).
Notation closed t := (tvars t = nil).
Notation fclosed r := (forall n, closed (r n)).

Lemma closed_notvars : forall t x, closed t -> x ∉ t.
Proof. intros t x Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve closed_notvars : term_db.

Lemma tvars_tsubs_closed : forall x u, closed u -> forall t,
  tvars t[u//x] = remove eq_dt_dec x (tvars t).
Proof. term_induction t; rewrite remove_app; f_equal; intuition. Qed.
Hint Rewrite tvars_tsubs_closed using intuition; fail : term_db.

Lemma notin_tsubs : forall x u t, x ∉ t -> t[u//x] = t.
Proof. term_induction t. Qed.
Hint Rewrite notin_tsubs using try easy;
                              (try (intuition; fail));
                              (try apply closed_notvars); intuition; fail : term_db.

Lemma tsubs_tsubs: forall x v y u, x <> y -> x ∉ u -> forall t,
  t[v//x][u//y] = t[u//y][v[u//y]//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tsubs using try (intuition; fail);
                              (try apply closed_notvars); intuition; fail : term_db.

Lemma notin_tsubs_bivar : forall x y t, x ∉ t -> t[tvar x//y][tvar y//x] = t.
Proof. term_induction t. Qed.
Hint Rewrite notin_tsubs_bivar using try easy;
                                    (try (intuition; fail));
                                    (try apply closed_notvars); intuition; fail : term_db.

End Fixed_Eigen_Type.


Section Two_Eigen_Types.

Variable T1 T2 : Type.
Variable r : T1 -> term T2 0.

Notation closed t := (tvars t = nil).
Notation fclosed := (forall n, closed (r n)).
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").

Hint Rewrite notin_tsubs using try easy;
                              (try (intuition; fail));
                              (try apply closed_notvars); intuition; fail : term_db.

(** * Additional results with variable eigen type *)

Lemma tvars_tesubs_fclosed : fclosed -> forall k (t : term T1 k), tvars t⟦r⟧ = tvars t.
Proof. term_induction t. Qed.
Hint Rewrite tvars_tesubs_fclosed using intuition; fail : term_db.

Lemma tsubs_tesubs : forall x u k (t : term T1 k), fclosed ->
  t[u//x]⟦r⟧ = t⟦r⟧[u⟦r⟧//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tesubs using intuition; fail : term_db.

End Two_Eigen_Types.


(* We restrict to [term nat] *)
Section Eigen_nat.

Hint Rewrite tvars_tesubs_fclosed using intuition; fail : term_db.

Notation term := (term nat).
Notation tvar := (tvar nat).
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").
Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation "x ∉ t" := (~ In x (tvars t)) (at level 30).
Notation closed t := (tvars t = nil).
Notation fclosed r := (forall n, closed (r n)).

Definition fup := fun n => evar (S n).
Notation "⇑" := fup.
Notation "t ↑" := (t⟦⇑⟧) (at level 8, format "t ↑").

Lemma fclosed_fup : fclosed ⇑.
Proof. reflexivity. Qed.
Hint Rewrite fclosed_fup : term_db.

Lemma tvars_fup : forall k (t : term k), tvars t↑ = tvars t.
Proof. rcauto. Qed.
Hint Rewrite tvars_fup : term_db.

Definition fesubs v := fun n =>
  match n with
  | 0 => v
  | S n => evar n
  end.
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").

Lemma fclosed_fesubs : forall v, closed v -> fclosed (v⇓).
Proof. intros v Hc n; now destruct n. Qed.
Hint Resolve fclosed_fesubs : term_db.

Lemma fesubs_fup v : ⇑ ;; v⇓ == evar.
Proof. intros ?; reflexivity. Qed.

Lemma tesubs_fup v k (t : term k) : t↑⟦v⇓⟧ = t.
Proof. rcauto. Qed.
Hint Rewrite tesubs_fup : term_db.

(* In practive only the case [u = evar 0] will be used *)
Definition felift u (r : _ -> term 0) := fun n =>
  match n with
  | 0 => u
  | S k => (r k)↑
  end.
Notation "⇑[ u ] r" := (felift u r) (at level 25, format "⇑[ u ] r").

Lemma fclosed_felift u r : closed u -> fclosed r -> fclosed (⇑[u]r).
Proof. intros ? ? n; rnow destruct n. Qed.
Hint Resolve fclosed_felift : term_db.

Lemma felift_comp u r : r ;; ⇑ == ⇑ ;; ⇑[u]r.
Proof. intros ?; reflexivity. Qed.
Hint Rewrite felift_comp : term_db.

Lemma felift_tesubs u r : forall k (t : term k), t⟦r⟧↑ = t↑⟦⇑[u]r⟧.
Proof. rcauto. Qed.
Hint Rewrite felift_tesubs : term_db.

End Eigen_nat.

End Terms.

Ltac term_induction t :=
  try (intros until t); (* to avoid name clashes in induction t *)
  let nn := fresh "n" in
  let xx := fresh "x" in
  let ff := fresh "f" in
  let kk := fresh "k" in
  let uu := fresh "u" in
  let ll := fresh "l" in
  let IHuu := fresh "IHu" in
  let IHll := fresh "IHl" in
  induction t as [nn | xx | ff | uu IHuu kk ll IHll]; try (now intuition); simpl; intros;
  try (apply (f_equal2 (fun x y => tconstr x y)); try (now intuition));
  try (now rcauto);
  try (now f_equal; rcauto).
