(* Definitions and Properties of First-Order Terms *)
(*   with holes in [nat] for de Bruijn indices *)

From Coq Require Export PeanoNat List.
From OLlibs Require Import List_more.
From OLlibs Require Export funtheory dectype.
From Quantifiers Require Export term_tactics.

Set Implicit Arguments.


(** * First-Order Terms *)

Section Terms.

Context {vatom : DecType} {tatom : Type}.

(** terms with quantifiable variables

    arity not given meaning that we have a copy of each function name for each arity

 - [evar] for De Bruijn style eigen variables in proofs,
             type for these indices as parameter called the eigen type,
             but mostly used with [nat].
             Other values can be used (for terms without indices, use [Empty_set]).
 - [tvar] for quantified variables in formulas *)
Inductive term T :=
| evar : T -> term T
| tvar : vatom -> term T
| tconstr : tatom -> list (term T) -> term T.
Arguments evar {T}.

(** appropriate induction for [term] (with list inside): so called "nested fix" *)
Fixpoint term_ind_list_Forall T t :
  forall P : term T -> Prop,
  (forall n, P (evar n)) ->
  (forall x, P (tvar T x)) ->
  (forall f l, Forall P l -> P (tconstr f l)) -> P t :=
fun P Pevar Ptvar Pconstr =>
match t with
| evar n => Pevar n
| tvar _ x => Ptvar x
| tconstr c l => Pconstr c l
    ((fix l_ind l' : Forall P l' :=
      match l' with
      | nil => Forall_nil P
      | cons t1 l1 => Forall_cons _
                        (term_ind_list_Forall t1 Pevar Ptvar Pconstr)
                        (l_ind l1)
      end) l)
end.
Ltac term_induction t :=
  (try intros until t);
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  apply (term_ind_list_Forall t);
  [ intros nn; try (now intuition); simpl
  | intros xx; try (now intuition); simpl
  | intros cc ll IHll; simpl; intros;
    try (apply (f_equal (tconstr _)));
    rewrite ? flat_map_concat_map, ? map_map;
    try (apply (f_equal (@concat _)));
    match goal with
    | |- map _ ?l = ?l => rewrite <- (map_id l) at 2
    | _ => idtac
    end;
    try (apply map_ext_in; intros i Hi; specialize_Forall_all i);
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i);
    try (intuition; fail) ];
  try (now rcauto).


(** * Monad structure on [term] via substitution *)

(** substitutes the [term] [r n] for index [n] in [term] [t] *)
Fixpoint tesubs T1 T2 (r : T1 -> term T2) (t : term T1) :=
match t with
| tvar _ x => tvar T2 x
| evar k => r k
| tconstr f l => tconstr f (map (tesubs r) l)
end.
Notation "t ⟦ r ⟧" := (tesubs r t) (at level 8, left associativity, format "t ⟦ r ⟧").

(** monad structure induced on [term] *)
Lemma evar_tesubs T1 T2 (r : T1 -> term T2) x : (evar x)⟦r⟧ = r x.
Proof. reflexivity. Qed.
Hint Rewrite evar_tesubs : term_db.

Lemma tesubs_evar T (t : term T) : t⟦evar⟧ = t.
Proof. term_induction t. Qed.
Hint Rewrite tesubs_evar : term_db.

Definition fecomp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) := fun x => (r x)⟦s⟧.
Notation "r ;; s" := (fecomp r s) (at level 20, format "r  ;;  s").

Lemma tesubs_comp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) t : t⟦r⟧⟦s⟧ = t⟦r ;; s⟧.
Proof. term_induction t. Qed.
Hint Rewrite tesubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma tesubs_ext T1 T2 (r1 r2 : T1 -> term T2) : r1 ~ r2 -> forall t, t⟦r1⟧ = t⟦r2⟧.
Proof. term_induction t. Qed.
Hint Resolve tesubs_ext : term_db.
(* TODO could be turned into a morphism *)


Section Fixed_Eigen_Type.

Variable T : Type.
Implicit Type t : term T.
Arguments tvar {T} _.

(** * Term substitution *)

(** substitutes [term] [u] for variable [x] in [term] [t] *)
Fixpoint tsubs x u t :=
match t with
| tvar y => if eq_dt_dec y x then u else tvar y
| evar k => evar k
| tconstr c l => tconstr c (map (tsubs x u) l)
end.
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").

Lemma tsubs_tsubs_eq : forall x u v t, t[v//x][u//x] = t[v[u//x]//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tsubs_eq : term_db.


(** * Variables *)

Fixpoint tvars t :=
match t with
| tvar x => x :: nil
| evar _ => nil
| tconstr _ l => flat_map tvars l
end.
Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation "x ∉ t" := (~ In x (tvars t)) (at level 30).
Notation closed t := (tvars t = nil).

Lemma closed_notvars t x : closed t -> x ∉ t.
Proof. intros -> []. Qed.
Hint Resolve closed_notvars : term_db.

Lemma tvars_tsubs_closed x u (Hc : closed u) t : tvars t[u//x] = remove eq_dt_dec x (tvars t).
Proof. term_induction t.
rewrite remove_concat, flat_map_concat_map, map_map. f_equal.
apply map_ext_in. intros v Hv. specialize_Forall IHl with v. exact IHl.
Qed.
Hint Rewrite tvars_tsubs_closed using intuition; fail : term_db.

Lemma notin_tsubs : forall x u t, x ∉ t -> t[u//x] = t.
Proof. term_induction t; try rcauto.
apply IHl. intros Hx. apply H, in_flat_map. exists i. split; assumption.
Qed.
Hint Rewrite notin_tsubs using try (intuition; fail); try apply closed_notvars; intuition; fail : term_db.

Lemma tsubs_tsubs x v y u : x <> y -> x ∉ u -> forall t,
  t[v//x][u//y] = t[u//y][v[u//y]//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tsubs using try (intuition; fail); try apply closed_notvars; intuition; fail : term_db.

Lemma notin_tsubs_bivar x y t : x ∉ t -> t[tvar x//y][tvar y//x] = t.
Proof. term_induction t.
apply IHl. intros Hx. apply H, in_flat_map. exists i. split; assumption.
Qed.
Hint Rewrite notin_tsubs_bivar using try (intuition; fail); try apply closed_notvars; (intuition; fail) : term_db.

End Fixed_Eigen_Type.


Section Two_Eigen_Types.

Variable T1 T2 : Type.
Variable r : T1 -> term T2.

Notation closed t := (tvars t = nil).
Notation rclosed := (forall n, closed (r n)).
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").

Hint Rewrite notin_tsubs using try (intuition; fail); try apply closed_notvars; intuition; fail : term_db.

(** * Additional results with variable eigen type *)

Lemma tvars_tesubs_closed t : rclosed -> tvars t⟦r⟧ = tvars t.
Proof. term_induction t. Qed.
Hint Rewrite tvars_tesubs_closed using intuition; fail : term_db.

Lemma tsubs_tesubs x u t : rclosed -> t[u//x]⟦r⟧ = t⟦r⟧[u⟦r⟧//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tesubs using intuition; fail : term_db.

End Two_Eigen_Types.


(* We restrict to [term nat] *)
Section Eigen_nat.

Hint Rewrite tvars_tesubs_closed using intuition; fail : term_db.

Notation term := (term nat).
Notation tvar := (tvar nat).
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").
Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation "x ∉ t" := (~ In x (tvars t)) (at level 30).
Notation closed t := (tvars t = nil).
Notation rclosed r := (forall n, closed (r n)).

Definition fup := fun n => evar (S n).
Notation "⇑" := fup.
Notation "t ↑" := (t⟦⇑⟧) (at level 8, format "t ↑").

Lemma closed_fup : rclosed ⇑.
Proof. reflexivity. Qed.
Hint Rewrite closed_fup : term_db.

Lemma tvars_fup t : tvars t↑ = tvars t.
Proof. rcauto. Qed.
Hint Rewrite tvars_fup : term_db.

(* general shape, unused, generated through ↑
Definition fesubs k v := fun n =>
  match n ?= k with
  | Lt => evar n
  | Eq => v
  | Gt => evar (pred n)
  end.
Notation "v // ↓ k" := (fesubs k v) (at level 18, format "v // ↓ k").

Lemma closed_fesubs : forall k v, closed v -> rclosed (v//↓k).
Proof. e_case_intuition unfolding fesubs. Qed.
Hint Resolve closed_fesubs : term_db.

Lemma fesubs_fup k v : ⇑ ;; v↑//↓(S k) == v//↓k ;; ⇑.
Proof. intros ?; unfold fesubs, fup, fecomp; e_case_intuition. Qed.
*)
Definition fesubs v := fun n =>
  match n with
  | 0 => v
  | S n => evar n
  end.
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").

Lemma closed_fesubs v : closed v -> rclosed (v⇓).
Proof. now intros Hc [|]. Qed.
Hint Resolve closed_fesubs : term_db.

Lemma fesubs_fup v : ⇑ ;; v⇓ ~ evar.
Proof. intro. reflexivity. Qed.

Lemma tesubs_fup v t : t↑⟦v⇓⟧ = t.
Proof. rcauto. Qed.
Hint Rewrite tesubs_fup : term_db.

(* In practive only the case [u = evar 0] will be used *)
Definition felift u r := fun n =>
  match n with
  | 0 => u
  | S k => (r k)↑
  end.
Notation "⇑[ u ] r" := (felift u r) (at level 25, format "⇑[ u ] r").

Lemma closed_felift u r : closed u -> rclosed r -> rclosed (⇑[u]r).
Proof. rnow intros ? ? [|]. Qed.
Hint Resolve closed_felift : term_db.

Lemma felift_comp u r : r ;; ⇑ ~ ⇑ ;; ⇑[u]r.
Proof. intro. reflexivity. Qed.
Hint Rewrite felift_comp : term_db.

Lemma felift_tesubs u r t : t⟦r⟧↑ = t↑⟦⇑[u]r⟧.
Proof. rcauto. Qed.
Hint Rewrite felift_tesubs : term_db.

End Eigen_nat.

End Terms.

Ltac term_induction t :=
  (try intros until t);
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  apply (term_ind_list_Forall t);
  [ intros nn; try (now intuition); simpl
  | intros xx; try (now intuition); simpl
  | intros cc ll IHll; simpl; intros;
    try (apply (f_equal (tconstr _)));
    rewrite ? flat_map_concat_map, ? map_map;
    try (apply (f_equal (@concat _)));
    match goal with
    | |- map _ ?l = ?l => rewrite <- (map_id l) at 2
    | _ => idtac
    end;
    try (apply map_ext_in; intros i Hi; specialize_Forall_all i);
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i);
    try (now intuition) ];
  try (now (rnow idtac)); try (now rcauto).
