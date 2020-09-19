(* Definitions and properties of first-order terms *)
(*   with holes in [nat] for de Bruijn indices *)

From Coq Require Export PeanoNat Lia List.

Require Import lib_files.List_more.
Require Export lib_files.dectype.

Require Export term_tactics.

Set Implicit Arguments.


(* Extensional equality of functions *)
Infix "==" := (fun f g => forall x, f x = g x) (at level 70).

Ltac e_case_analysis :=
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
Ltac e_case_intuition := repeat e_case_analysis; (try now intuition); (try (exfalso; lia)).
(* [ne_reference_list] would be better below, but apparently not available, see Ltac2? *)
(*   see also https://github.com/coq/coq/issues/11209 *)
Tactic Notation "e_case_intuition" "unfolding" reference(ref) :=
  intros; unfold ref; e_case_intuition.



(** * First-Order Terms *)

Section Terms.

Context { vatom : DecType } { tatom : Type }.

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
(** [evar] for De Bruijn style eigen variables in proofs *)
(**          type for these indices as parameter called the eigen type *)
(**          but mostly used with [nat] *)
(**          other values can be used for terms without indices (use [Empty_set]) *)
(**          or for mapping into other syntaxes *)
(** [tvar] for quantified variables in formulas *)
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
Lemma evar_tesubs T1 T2 (r : T1 -> term T2) :
  forall x, (evar x)⟦r⟧ = r x.
Proof. reflexivity. Qed.
Hint Rewrite evar_tesubs : term_db.

Lemma tesubs_evar T : forall (t : term T),
  t⟦evar⟧ = t.
Proof. term_induction t. Qed.
Hint Rewrite tesubs_evar : term_db.

Definition fecomp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) := fun x => (r x)⟦s⟧.
Notation "r ;; s" := (fecomp r s) (at level 20, format "r  ;;  s").

Lemma tesubs_comp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) :
  forall t, t⟦r⟧⟦s⟧ = t⟦r ;; s⟧.
Proof. term_induction t. Qed.
Hint Rewrite tesubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma tesubs_ext T1 T2 (r1 r2 : T1 -> term T2) :
  r1 == r2 -> forall t, t⟦r1⟧ = t⟦r2⟧.
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
| tvar y => if (eqb y x) then u else tvar y
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
Notation fclosed r := (forall n, closed (r n)).

Lemma closed_notvars : forall t x, closed t -> x ∉ t.
Proof. intros t x Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve closed_notvars : term_db.

Lemma tvars_tsubs_closed : forall x u, closed u -> forall t,
  tvars t[u//x] = remove eq_dt_dec x (tvars t).
Proof. term_induction t.
rewrite remove_concat, flat_map_concat_map, map_map; f_equal.
apply map_ext_in; intros v Hv; now specialize_Forall IHl with v.
Qed.
Hint Rewrite tvars_tsubs_closed using intuition; fail : term_db.

(*
Lemma tvars_tsubs : forall x y u t,
  x ∈ t[u//y] <-> (x ∈ u /\ y ∈ t) \/ (x ∈ t /\ x <> y).
Proof. split; term_induction t.
- e_case_intuition.
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
*)

Lemma notin_tsubs : forall x u t, x ∉ t -> t[u//x] = t.
Proof. term_induction t; try rcauto; f_equal.
apply IHl; intros Hx; apply H, in_flat_map; exists i; intuition.
Qed.
Hint Rewrite notin_tsubs using try easy;
                              (try (intuition; fail));
                              (try apply closed_notvars); intuition; fail : term_db.

Lemma tsubs_tsubs: forall x v y u, x <> y -> x ∉ u -> forall t,
  t[v//x][u//y] = t[u//y][v[u//y]//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tsubs using try (intuition; fail);
                              (try apply closed_notvars); intuition; fail : term_db.

Lemma notin_tsubs_bivar : forall x y t, x ∉ t -> t[tvar x//y][tvar y//x] = t.
Proof. term_induction t.
apply IHl; intros Hx; apply H, in_flat_map; exists i; intuition.
Qed.
Hint Rewrite notin_tsubs_bivar using try easy;
                                    (try (intuition; fail));
                                    (try apply closed_notvars); intuition; fail : term_db.

(*
(** * Iterated substitution *)

Definition multi_tsubs L t := fold_left (fun v '(x,u) => v[u//x]) L t.
Notation "t [[ L ]]" := (multi_tsubs L t) (at level 8, format "t [[ L ]]").

Lemma multi_tsubs_nil : multi_tsubs nil = id.
Proof. reflexivity. Qed.
Hint Rewrite multi_tsubs_nil : term_db.

Lemma multi_tsubs_evar : forall L n, (evar n)[[L]] = evar n.
Proof. now induction L; simpl; intros n; [ | destruct a; rewrite IHL ]. Qed.
Hint Rewrite multi_tsubs_evar : term_db.

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
- now apply incl_l_nil.
- destruct a; simpl; simpl in Hc, Hf; inversion_clear Hc.
  apply IHL; intuition.
  intros z Hinz.
  rewrite tvars_tsubs_closed in Hinz by assumption.
  apply in_remove in Hinz; destruct Hinz as [Hinz Hneq].
  apply Hf in Hinz; inversion Hinz; [ exfalso | ]; intuition.
Qed.

Lemma multi_tsubs_tsubs : forall L x u,
  ~ In x (map fst L) -> Forall (fun z => x ∉ snd z) L ->
  forall t, t[u//x][[L]] = t[[L]][u[[L]]//x].
Proof.
induction L; simpl; intros x v Hnin HF t; [ reflexivity | destruct a ].
inversion_clear HF; rewrite tsubs_tsubs, IHL; intuition.
Qed.
Hint Rewrite multi_tsubs_tsubs using intuition; fail : term_db.
*)
End Fixed_Eigen_Type.

Section Two_Eigen_Types.

Variable T1 T2 : Type.
Variable r : T1 -> term T2.

Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation "x ∉ t" := (~ In x (tvars t)) (at level 30).
Notation closed t := (tvars t = nil).
Notation fclosed := (forall n, closed (r n)).
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").
(*
Notation "t [[ L ]]" := (multi_tsubs L t) (at level 8, format "t [[ L ]]").
*)

Hint Rewrite notin_tsubs using try easy;
                              (try (intuition; fail));
                              (try apply closed_notvars); intuition; fail : term_db.
Hint Resolve closed_notvars : term_db.


(** * Additional results with variable eigen type *)

Lemma tvars_tesubs_fclosed : fclosed -> forall t, tvars t⟦r⟧ = tvars t.
Proof. term_induction t. Qed.
Hint Rewrite tvars_tesubs_fclosed using intuition; fail : term_db.

Lemma tsubs_tesubs : forall x u t, fclosed ->
  t[u//x]⟦r⟧ = t⟦r⟧[u⟦r⟧//x].
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tesubs using intuition; fail : term_db.

(*
Lemma tvars_tesubs : forall t, incl (tvars t) (tvars t⟦r⟧).
Proof. term_induction t.
rewrite <- 2 flat_map_concat_map.
intros x Hin.
apply in_flat_map in Hin; destruct Hin as [ u [Huin Hinu] ].
specialize_Forall IHl with u.
apply in_flat_map; exists u; intuition.
Qed.

(** * No capture generated by [r] in [t] under virtual binders for [l] *)

Fixpoint no_tecapture_at lv t :=
match t with
| evar n => Forall (fun x => x ∉ (r n)) lv
| tvar _ x => True
| tconstr f l => fold_right (fun u P => and (no_tecapture_at lv u) P) True l
end.
Notation "#[[ lv ]] t" := (no_tecapture_at lv t) (at level 30, format "#[[ lv ]]  t").

Lemma no_tecapture_less : forall lv1 lv2 t, incl lv1 lv2 ->
  #[[lv2]] t -> #[[lv1]] t.
Proof. term_induction t.
- intro; apply incl_Forall; intuition.
- apply Forall_fold_right in H0.
  apply Forall_fold_right, Forall_forall; intros u Hu.
  specialize_Forall_all u; intuition.
Qed.

Lemma fclosed_no_tecapture : fclosed -> forall lv t, #[[lv]] t.
Proof. intros Hc; term_induction t.
- rewrite (Hc n).
  apply Forall_forall; auto.
- now apply Forall_fold_right.
Qed.
Hint Resolve fclosed_no_tecapture : term_db.

Lemma tsubs_tesubs_notecap : forall x u t, #[[x::nil]] t ->
  t[u//x]⟦r⟧ = t⟦r⟧[u⟦r⟧//x].
Proof. term_induction t.
- intros HF; rnow inversion_clear HF.
- apply Forall_fold_right, Forall_forall with (x:=i) in H; intuition.
Qed.
Hint Rewrite tsubs_tesubs using try (intuition; fail);
                               (try apply fclosed_no_tecapture); intuition; fail : term_db.

Lemma tesubs_tvars : forall x u, #[[x::nil]] u -> x ∈ u⟦r⟧ -> x ∈ u.
Proof. term_induction u.
- now intros HF Hin; inversion_clear HF.
- apply Forall_fold_right in H.
  rewrite flat_map_map in H0; apply in_flat_map in H0; destruct H0 as [ v [Hvin Hinv] ].
  specialize_Forall_all v.
  rewrite <- flat_map_concat_map.
  apply in_flat_map; exists v; intuition.
Qed.

Lemma multi_tsubs_tesubs : forall L t, fclosed ->
  t[[L]]⟦r⟧ = t⟦r⟧[[map (fun '(x,u) => (x, tesubs r u)) L]].
Proof. induction L; simpl; intros t HF; [ reflexivity | ].
destruct a; rewrite IHL, tsubs_tesubs; intuition.
Qed.
Hint Rewrite multi_tsubs_tesubs : term_db.

Lemma no_tecapture_subs_notin : forall x u y t,
  closed u -> #[[y::nil]] t[u//x] -> y ∈ u⟦r⟧ -> x ∉ t.
Proof. term_induction t.
- intros Hc Hnc Hinu Hint.
  destruct Hint; subst; intuition.
  revert Hnc; case_analysis; intros Hnc.
  apply tesubs_tvars in Hnc; [ | assumption ].
  now revert Hnc; apply closed_notvars.
  (* TODO automatize? difference between [~ A] and [A -> False]
     revert Hnc; apply (proj1 (neg_false (y ∈ u))).
     auto with term_db. *)
- intros Hint.
  apply Forall_fold_right in H0.
  apply in_flat_map in Hint; destruct Hint as [ z [Hinzl Hinz] ].
  apply in_map_iff in Hinzl.
  destruct Hinzl as [ v [Heq Hz] ]; subst.
  specialize_Forall_all v.
  apply in_map with (f:= tsubs x u) in Hz.
  specialize_Forall H0 with (tsubs x u v).
  now apply IHl.
Qed.
*)
End Two_Eigen_Types.

(* We restrict to [term nat] *)
Section Eigen_nat.

Hint Rewrite tvars_tesubs_fclosed using intuition; fail : term_db.

(*
(** * Eigen variables *)
Fixpoint teigen_max t :=
match t with
| tvar _ _ => 0
| evar n => n
| tconstr _ l => list_max (map teigen_max l)
end.
*)

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

Lemma tvars_fup : forall t, tvars t↑ = tvars t.
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

Lemma fclosed_fesubs : forall k v, closed v -> fclosed (v//↓k).
Proof. e_case_intuition unfolding fesubs. Qed.
Hint Resolve fclosed_fesubs : term_db.

Lemma fesubs_fup k v : ⇑ ;; v↑//↓(S k) == v//↓k ;; ⇑.
Proof. intros ?; unfold fesubs, fup, fecomp; e_case_intuition. Qed.
*)
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

Lemma fclosed_felift u r : closed u -> fclosed r -> fclosed (⇑[u]r).
Proof. intros ? ? n; rnow destruct n. Qed.
Hint Resolve fclosed_felift : term_db.

Lemma felift_comp u r : r ;; ⇑ == ⇑ ;; ⇑[u]r.
Proof. intros ?; reflexivity. Qed.
Hint Rewrite felift_comp : term_db.

Lemma felift_tesubs u r : forall t, t⟦r⟧↑ = t↑⟦⇑[u]r⟧.
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
