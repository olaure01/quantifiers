(* Definitions and properties of first-order terms *)
(*   with holes in [nat] for de Bruijn indices *)

Require Export PeanoNat Compare_dec Lia List.
Require Import stdlib_more.
Require Export dectype term_tactics.

Set Implicit Arguments.


(* Extensional equality of functions *)
Infix "==" := (fun f g => forall x, f x = g x) (at level 70).

Ltac db_case_analysis :=
let Heq := fresh "Heq" in
let Heqeq := fresh "Heqeq" in
match goal with
| |- context f [?x =? ?y] => case_eq (x =? y); intros Heq
| |- context f [?x <? ?y] => case_eq (x <? y); intros Heq
| |- context f [?x ?= ?y] => case_eq (x ?= y); intros Heq;
                             [ rewrite Nat.compare_eq_iff in Heq
                             | rewrite Nat.compare_lt_iff in Heq
                             | rewrite Nat.compare_gt_iff in Heq ]
| |- context f [eqb ?x ?x] => rewrite (eqb_refl x)
| |- context f [eqb ?x ?y] => case eq_dt_reflect; intros Heq; [ try subst x | ]
| |- context f [eq_dt_dec ?x ?x] => rewrite (if_eq_dt_dec_refl x)
| H : ?x <> ?y |- context f [eq_dt_dec ?x ?y] => rewrite (if_eq_dt_dec_neq x y H)
| H : ?y <> ?x |- context f [eq_dt_dec ?x ?y] => rewrite (if_eq_dt_dec_neq x y (not_eq_sym H))
| |- context f [eq_dt_dec ?x ?y] => case_eq (eq_dt_dec x y); intros Heq Heqeq; [ subst x | ]
end; simpl.
Ltac db_case_intuition := repeat db_case_analysis; (try now intuition); (try (exfalso; lia)).
(* [ne_reference_list] would be better below, but apparently not available, see Ltac2? *)
(*   see also https://github.com/coq/coq/issues/11209 *)
Tactic Notation "db_case_intuition" "unfolding" reference(ref) :=
  intros; unfold ref; db_case_intuition.



(** * First-Order Terms *)

Section Terms.

Context { vatom : DecType } { tatom : Type }.

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
(** [dvar] for De Bruijn style eigen variables in proofs *)
(**          type for these indices as parameter called the eigen type *)
(**          but mostly used with [nat] *)
(**          other values can be used for terms without indices (use [Empty_set]) *)
(**          or for mapping into other syntaxes *)
(** [tvar] for quantified variables in formulas *)
Inductive term T :=
| dvar : T -> term T
| tvar : vatom -> term T
| tconstr : tatom -> list (term T) -> term T.
Arguments dvar {T}.

(** appropriate induction for [term] (with list inside): so called "nested fix" *)
Fixpoint term_ind_list_Forall T t :
  forall P : term T -> Prop,
  (forall n, P (dvar n)) ->
  (forall x, P (tvar T x)) ->
  (forall f l, Forall P l -> P (tconstr f l)) -> P t :=
fun P Pdvar Ptvar Pconstr =>
match t with
| dvar n => Pdvar n
| tvar _ x => Ptvar x
| tconstr c l => Pconstr c l
    ((fix l_ind l' : Forall P l' :=
      match l' with
      | nil => Forall_nil P
      | cons t1 l1 => Forall_cons _
                        (term_ind_list_Forall t1 Pdvar Ptvar Pconstr)
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
    try (now intuition) ];
  try (now (rnow idtac)); try (now rcauto).


(** * Monad structure on [term] via substitution *)

(** substitutes the [term] [r n] for index [n] in [term] [t] *)
Fixpoint tdbsubs T1 T2 (r : T1 -> term T2) (t : term T1) :=
match t with
| tvar _ x => tvar T2 x
| dvar k => r k
| tconstr f l => tconstr f (map (tdbsubs r) l)
end.
Notation "t ⟦ r ⟧" := (tdbsubs r t) (at level 8, left associativity, format "t ⟦ r ⟧").

(** monad structure induced on [term] *)
Lemma dvar_tdbsubs T1 T2 (r : T1 -> term T2) :
  forall x, (dvar x)⟦r⟧ = r x.
Proof. reflexivity. Qed.
Hint Rewrite dvar_tdbsubs : term_db.

Lemma tdbsubs_dvar T : forall (t : term T),
  t⟦dvar⟧ = t.
Proof. term_induction t. Qed.
Hint Rewrite tdbsubs_dvar : term_db.

Definition fdbcomp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) := fun x => (r x)⟦s⟧.
Notation "r ;; s" := (fdbcomp r s) (at level 20, format "r  ;;  s").

Lemma tdbsubs_comp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) :
  forall t, t⟦r⟧⟦s⟧ = t⟦r ;; s⟧.
Proof. term_induction t. Qed.
Hint Rewrite tdbsubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma tdbsubs_ext T1 T2 (r1 r2 : T1 -> term T2) :
  r1 == r2 -> forall t, t⟦r1⟧ = t⟦r2⟧.
Proof. term_induction t. Qed.
Hint Resolve tdbsubs_ext : term_db.


Section Fixed_Eigen_Type.

Variable T : Type.
Implicit Type t : term T.
Arguments tvar {T} _.

(** * Term substitution *)

(** substitutes [term] [u] for variable [x] in [term] [t] *)
Fixpoint tsubs x u t :=
match t with
| tvar y => if (eqb y x) then u else tvar y
| dvar k => dvar k
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
| dvar _ => nil
| tconstr _ l => flat_map tvars l
end.
Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation "x ∉ r" := (forall n, ~ x ∈ r n) (at level 30).
Notation closed t := (tvars t = nil).
Notation rclosed r := (forall n, closed (r n)).

Lemma closed_notvars : forall t x, closed t -> ~ x ∈ t.
Proof. intros t x Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve closed_notvars : term_db.

Lemma rclosed_notvars T0 : forall (r : T0 -> term T) x, rclosed r -> x ∉ r.
Proof. intros r x Hc n Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve rclosed_notvars : term_db.

Lemma tvars_tdbsubs_closed : forall r, rclosed r -> forall t,
  tvars t⟦r⟧ = tvars t.
Proof. term_induction t. Qed.
Hint Rewrite tvars_tdbsubs_closed using intuition; fail : term_db.

Lemma tvars_tsubs_closed : forall x u, closed u -> forall t,
  tvars t[u//x] = remove eq_dt_dec x (tvars t).
Proof. term_induction t.
rewrite remove_concat, flat_map_concat_map, map_map; f_equal.
apply map_ext_in; intros v Hv; now specialize_Forall IHl with v.
Qed.
Hint Rewrite tvars_tsubs_closed using intuition; fail : term_db.

Lemma tvars_tsubs : forall x y u t,
  x ∈ t[u//y] <-> (x ∈ u /\ y ∈ t) \/ (x ∈ t /\ x <> y).
Proof. split; term_induction t.
- db_case_intuition.
  intros Heq2; right; intuition; subst; intuition.
- revert H IHl; induction l; simpl; intros Hin Hl.
  + inversion Hin.
  + inversion_clear Hl.
    rewrite_all in_app_iff; intuition.
- destruct H as [[Hin1 Hin2]|[Hin Hneq]].
  + revert IHl; induction l; simpl; intros Hl; [ inversion Hin2 | ].
    inversion_clear Hl; in_solve.
  + revert IHl; induction l; simpl; intros Hl; [ inversion Hin | ].
    inversion_clear Hl; in_solve.
Qed.

Lemma notin_tsubs : forall x u t, ~ x ∈ t -> t[u//x] = t.
Proof. term_induction t; try rcauto; f_equal.
apply IHl; intros Hx; apply H, in_flat_map; exists i; intuition.
Qed.
Hint Rewrite notin_tsubs using try easy;
                              (try (intuition; fail));
                              (try apply closed_notvars); intuition; fail : term_db.

Lemma tsubs_tsubs: forall x v y u, x <> y -> ~ x ∈ u -> forall t,
  t[v//x][u//y] = t[u//y][v[u//y]//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tsubs using try (intuition; fail);
                              (try apply closed_notvars); intuition; fail : term_db.

Lemma notin_tsubs_bivar : forall x y t, ~ x ∈ t -> t[tvar x//y][tvar y//x] = t.
Proof. term_induction t.
apply IHl; intros Hx; apply H, in_flat_map; exists i; intuition.
Qed.
Hint Rewrite notin_tsubs_bivar using try easy;
                                    (try (intuition; fail));
                                    (try apply closed_notvars); intuition; fail : term_db.

Lemma tsubs_tdbsubs : forall x u r, x ∉ r -> forall t,
  t[u//x]⟦r⟧ = t⟦r⟧[u⟦r⟧//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tdbsubs using try (intuition; fail);
                                (try apply rclosed_notvars); intuition; fail : term_db.


(** * Iterated substitution *)

Definition multi_tsubs L t := fold_left (fun v '(x,u) => v[u//x]) L t.
Notation "t [[ L ]]" := (multi_tsubs L t) (at level 8, format "t [[ L ]]").

Lemma multi_tsubs_nil : multi_tsubs nil = id.
Proof. reflexivity. Qed.
Hint Rewrite multi_tsubs_nil : term_db.

Lemma multi_tsubs_dvar : forall L n, (dvar n)[[L]] = dvar n.
Proof. now induction L; simpl; intros n; [ | destruct a; rewrite IHL ]. Qed.
Hint Rewrite multi_tsubs_dvar : term_db.

Lemma multi_tsubs_tvar : forall L x, ~ In x (map fst L) -> (tvar x)[[L]] = tvar x.
Proof.
induction L; intros x Hin; simpl; [ reflexivity | destruct a; case_analysis ].
- exfalso; now apply Hin; left.
- apply IHL.
  now intros Hin2; apply Hin; right.
Qed.
Hint Rewrite multi_tsubs_tvar using intuition; fail : term_db.

Lemma multi_tsubs_tconstr : forall L f l,
  (tconstr f l)[[L]] = tconstr f (map (multi_tsubs L) l).
Proof.
induction L; intros f l; simpl.
- rnow f_equal then rewrite map_id.
- now destruct a; rewrite IHL, map_map.
Qed.
Hint Rewrite multi_tsubs_tconstr : term_db.

Lemma closed_multi_tsubs : forall L t, closed t -> t[[L]] = t.
Proof. induction L; intros t Hc; rcauto. Qed.
Hint Rewrite closed_multi_tsubs using intuition; fail : term_db.

Lemma multi_tsubs_closed : forall L t,
  Forall (fun u => closed u) (map snd L) -> incl (tvars t) (map fst L) ->
  closed t[[L]].
Proof.
induction L; simpl; intros t Hc Hf.
- now apply incl_nil_inv.
- destruct a; simpl; simpl in Hc, Hf; inversion_clear Hc.
  apply IHL; intuition.
  intros z Hinz.
  rewrite tvars_tsubs_closed in Hinz by assumption.
  apply in_remove in Hinz; destruct Hinz as [Hinz Hneq].
  apply Hf in Hinz; inversion Hinz; [ exfalso | ]; intuition.
Qed.

Lemma multi_tsubs_tdbsubs : forall L r t,
  Forall (fun x => x ∉ r) (map fst L) ->
  t[[L]]⟦r⟧ = t⟦r⟧[[map (fun '(x,u) => (x, tdbsubs r u)) L]].
Proof. induction L; simpl; intros r t HF; [ reflexivity | ].
destruct a; simpl in HF; inversion_clear HF.
now rewrite IHL, tsubs_tdbsubs.
Qed.
Hint Rewrite multi_tsubs_tdbsubs : term_db.

Lemma multi_tsubs_tsubs : forall L x u,
  ~ In x (map fst L) -> Forall (fun z => ~ x ∈ snd z) L ->
  forall t, t[u//x][[L]] = t[[L]][u[[L]]//x].
Proof.
induction L; simpl; intros x v Hnin HF t; [ reflexivity | destruct a ].
inversion_clear HF; rewrite tsubs_tsubs, IHL; intuition.
Qed.
Hint Rewrite multi_tsubs_tsubs using intuition; fail : term_db.

End Fixed_Eigen_Type.


(* We restrict to [term nat] *)
Section Eigen_nat.

(** * Eigen variables *)

Fixpoint teigen_max t :=
match t with
| tvar _ _ => 0
| dvar n => n
| tconstr _ l => list_max (map teigen_max l)
end.

Notation term := (term nat).
Notation tvar := (tvar nat).
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").
Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation closed t := (tvars t = nil).
Notation rclosed r := (forall n, closed (r n)).

(* TODO useless?
Definition tup k := fun n => dvar (if n <? k then n else S n).
Notation "⇑_ k" := (tup k) (at level 15).
Notation "⇑" := (tup 0).
*)
Definition tup := fun n => dvar (S n).
Notation "⇑" := tup.
Notation "t ↑" := (t⟦⇑⟧) (at level 8, format "t ↑").

Lemma rclosed_tup : rclosed ⇑.
Proof. reflexivity. Qed.

Definition fdbsubs k v := fun n =>
  match n ?= k with
  | Lt => dvar n
  | Eq => v
  | Gt => dvar (pred n)
  end.
Notation "v // ↓ k" := (fdbsubs k v) (at level 18, format "v // ↓ k").

Lemma closed_fdbsubs : forall k v, closed v -> rclosed (v//↓k).
Proof. db_case_intuition unfolding fdbsubs. Qed.

Lemma fdbsubs_tup k v : v//↓k ;; ⇑ == ⇑ ;; v↑//↓(S k).
Proof. intros ?; unfold fdbsubs, tup, fdbcomp; db_case_intuition. Qed.
Hint Rewrite fdbsubs_tup : term_db.

Lemma fdbsubs_z_tup v : dvar == ⇑ ;; v↑//↓0.
Proof. intros ?; reflexivity. Qed.
Hint Rewrite fdbsubs_z_tup : term_db.

Definition fdblift r := fun n =>
  match n with
  | 0 => dvar 0
  | S k => (r k)↑
  end.
Notation "↑ r" := (fdblift r) (at level 25, format "↑ r").

Lemma fdblift_comp r : r ;; ⇑ == ⇑ ;; ↑r.
Proof. intros ?; reflexivity. Qed.

Lemma lift_tdbsubs r : forall t, t⟦r⟧↑ = t↑⟦↑r⟧.
Proof. intros; rewrite 2 tdbsubs_comp; apply tdbsubs_ext, fdblift_comp. Qed.
Hint Rewrite lift_tdbsubs : term_db.

End Eigen_nat.

End Terms.

