(* Hilbert system for Intuitionistic Logic with implication and quantifiers *)

Require Import List.
Require Import stdlib_more.
Require Import dectype term_tactics.

Set Implicit Arguments.


(** * First-Order Terms *)

Section Terms.

Context { vatom : DecType } { tatom : Type }.

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
Inductive hterm :=
| hvar : vatom -> hterm
| hconstr : tatom -> list hterm -> hterm.

(** appropriate induction for [term] (with list inside): so called "nested fix" *)
Fixpoint hterm_ind_list_Forall t :
  forall P : hterm -> Prop,
  (forall x, P (hvar x)) ->
  (forall f l, Forall P l -> P (hconstr f l)) -> P t :=
fun P Phvar Pconstr =>
match t with
| hvar x => Phvar x
| hconstr c l => Pconstr c l
    ((fix l_ind l' : Forall P l' :=
      match l' with
      | nil => Forall_nil P
      | cons t1 l1 => Forall_cons _
                        (hterm_ind_list_Forall t1 Phvar Pconstr)
                        (l_ind l1)
      end) l)
end.
Ltac hterm_induction t :=
  (try intros until t);
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  apply (hterm_ind_list_Forall t);
  [ intros xx; try (now intuition); simpl
  | intros cc ll IHll; simpl;
    rewrite ? flat_map_concat_map; rewrite ? map_map;
    try f_equal;
    try (apply map_ext_in; intros i Hi; specialize_Forall_all i);
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i);
    try (now intuition) ];
  try (now (rnow idtac)); try (now rcauto).


(** * Term substitutions *)

(** substitutes [term] [u] for variable [x] in [term] [t] *)
Fixpoint htsubs x u t :=
match t with
| hvar y => if eqb y x then u else hvar y
| hconstr c l => hconstr c (map (htsubs x u) l)
end.


(** ** Free variables *)
Fixpoint hfreevars t :=
match t with
| hvar x => x :: nil
| hconstr f l => flat_map hfreevars l
end.
Notation hclosed t := (hfreevars t = nil).

Lemma hclosed_nohfreevars : forall t x, hclosed t -> ~ In x (hfreevars t).
Proof. intros t x Hc Hin; now rewrite Hc in Hin. Qed.
Hint Resolve hclosed_nohfreevars : term_db.

Lemma nfree_htsubs : forall x u t, ~ In x (hfreevars t) -> htsubs x u t = t.
Proof. hterm_induction t ; try rcauto; f_equal.
rewrite <- flat_map_concat_map in H; apply notin_flat_map_Forall in H.
rewrite <- (map_id l) at 2; apply map_ext_in; intros v Hv.
specialize_Forall_all v; intuition.
Qed.
Hint Rewrite nfree_htsubs using try (intuition; fail) ;
                               (try apply hclosed_nohfreevars); intuition; fail : term_db.

Lemma htsubs_htsubs_com : forall x v y u, x <> y -> ~ In x (hfreevars u) -> forall t,
  htsubs y u (htsubs x v t) = htsubs x (htsubs y u v) (htsubs y u t).
Proof. hterm_induction t. Qed.
Hint Rewrite htsubs_htsubs_com using try (intuition; fail);
                                    (try apply hclosed_nohfreevars); intuition; fail : term_db.

Lemma hfreevars_tsubs_closed : forall x u, hclosed u -> forall t,
  hfreevars (htsubs x u t) = remove eq_dt_dec x (hfreevars t).
Proof. hterm_induction t.
rewrite remove_concat, flat_map_concat_map, map_map; f_equal.
apply map_ext_in; intros v Hv; now specialize_Forall IHl with v.
Qed.
Hint Rewrite hfreevars_tsubs_closed using intuition; fail : term_db.

Lemma hfreevars_tsubs : forall x y u t, In x (hfreevars (htsubs y u t)) ->
  (In x (hfreevars u) /\ In y (hfreevars t)) \/ (In x (hfreevars t) /\ x <> y).
Proof. hterm_induction t.
- case_analysis.
  + intros Hin; left; intuition.
  + intros Heq2; right; intuition; subst; intuition.
- revert IHl; induction l; simpl; intros Hl Hin.
  + inversion Hin.
  + inversion_clear Hl.
    rewrite_all in_app_iff; intuition.
Qed.

Lemma hfreevars_to_tsubs : forall t x y u,
  In y (hfreevars t) -> In x (hfreevars u) -> In x (hfreevars (htsubs y u t)).
Proof. hterm_induction t; intros z y u Hin1 Hin2.
- case_analysis; intuition.
- revert IHl Hin1; induction l; simpl; intros Hl Hin; [ inversion Hin | ].
  inversion_clear Hl; in_solve.
Qed.

Lemma htbisubs : forall x y t, ~ In x (hfreevars t) ->
  htsubs x (hvar y) (htsubs y (hvar x) t) = t.
Proof. hterm_induction t; intros Hin; f_equal.
rewrite <- (map_id l) at 2.
apply map_ext_in; intros z Hz.
specialize_Forall IHl with z; apply IHl.
intros Hin2; apply Hin.
now rewrite <- flat_map_concat_map; apply in_flat_map with z.
Qed.

End Terms.



(* Formulas and Proofs *)

Section Formulas.

Context { vatom : DecType } { tatom : Type } { fatom : Type }.
Notation hterm := (@hterm vatom tatom).
Notation hclosed t := (hfreevars t = nil).

(** formulas *)
(** first-order formulas in the langage: implication, universal quantification *)
Inductive hformula :=
| hfvar : fatom -> list hterm -> hformula
| himp : hformula -> hformula -> hformula
| hfrl : vatom -> hformula -> hformula
| hexs : vatom -> hformula -> hformula.
Infix "⟶" := himp (at level 70, right associativity).

Ltac hformula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | A1 A2 | xx A | xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try f_equal; try (induction ll as [ | tt lll IHll ]; simpl; intuition;
                      rewrite IHll; f_equal; intuition)
  | try (f_equal; intuition)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail) ];
  try (now (rnow idtac)); try (now rcauto).

Fixpoint hfsize A :=
match A with
| hfvar _ _ => 1
| himp B C => S (hfsize B + hfsize C)
| hfrl _ B => S (hfsize B)
| hexs _ B => S (hfsize B)
end.

Fixpoint hffreevars A :=
match A with
| hfvar _ l => flat_map hfreevars l
| himp B C => hffreevars B ++ hffreevars C
| hfrl x B => remove eq_dt_dec x (hffreevars B)
| hexs x B => remove eq_dt_dec x (hffreevars B)
end.

Lemma in_hffreevars_frl : forall x y, y <> x -> forall A,
  In x (hffreevars A) -> In x (hffreevars (hfrl y A)).
Proof.
hformula_induction A; apply notin_remove; intuition.
now rewrite <- flat_map_concat_map.
Qed.

Fixpoint hgood_for x y A :=
match A with
| hfvar X l => True
| himp B C => hgood_for x y B /\ hgood_for x y C
| hfrl z B => In x (hffreevars (hfrl z B)) -> hgood_for x y B /\ y <> z
| hexs z B => In x (hffreevars (hexs z B)) -> hgood_for x y B /\ y <> z
end.

(** substitutes [hterm] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint hfsubs x u A :=
match A with
| hfvar X l => hfvar X (map (htsubs x u) l)
| himp B C => himp (hfsubs x u B) (hfsubs x u C)
| hfrl y B => hfrl y (if eqb y x then B else hfsubs x u B)
| hexs y B => hexs y (if eqb y x then B else hfsubs x u B)
end.

Lemma hfsize_subs : forall u x A, hfsize (hfsubs x u A) = hfsize A.
Proof. hformula_induction A. Qed.
Hint Rewrite hfsize_subs : term_db.

Lemma nfree_hfsubs : forall x u A, ~ In x (hffreevars A) -> hfsubs x u A = A.
Proof. hformula_induction A; try rcauto.
- rnow apply nfree_htsubs then apply H.
- rnow apply H.
- rnow rewrite IHA.
  now apply H; apply in_hffreevars_frl.
- rnow rewrite IHA.
  now apply H; apply in_hffreevars_frl.
Qed.
Hint Rewrite nfree_hfsubs using intuition ; fail : term_db.

Lemma hffreevars_subs : forall x y u A, In x (hffreevars (hfsubs y u A)) ->
  (In x (hfreevars u) /\ In y (hffreevars A)) \/ (In x (hffreevars A) /\ x <> y).
Proof. hformula_induction A; try in_solve.
- revert H; induction l; simpl; intros Hin.
  + inversion Hin.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    * apply hfreevars_tsubs in Hin; in_solve.
    * apply IHl in Hin; in_solve.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  revert H; case_analysis; intros H.
  + right; intuition.
    apply in_remove in H; intuition.
  + assert (Hin := proj1 (in_remove _ _ _ _ H)).
    apply IHA in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition;
      apply notin_remove; intuition.
    subst; revert H; apply remove_In.
Qed.

Lemma hffreevars_to_subs : forall A x y t, hgood_for y x A ->
  In y (hffreevars A) -> In x (hfreevars t) -> In x (hffreevars (hfsubs y t A)).
Proof. hformula_induction A; try in_solve.
- revert H0 H1; clear; induction l; intros Hin1 Hin2; simpl; intuition.
  simpl in Hin1.
  apply in_or_app; apply in_app_or in Hin1; destruct Hin1 as [Hin1|Hin1]; [left|right].
  + now apply hfreevars_to_tsubs.
  + now apply IHl.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  apply in_remove in H0; destruct H0 as [Hin Hneq].
  case_analysis; intuition.
  assert (Hin2 := notin_remove eq_dt_dec _ _ x Hneq Hin).
  apply notin_remove; intuition.
Qed.


(* All variables occurring (free or bound or for quantification) in a formula *)
Fixpoint hallvars A :=
match A with
| hfvar _ l => concat (map hfreevars l)
| himp B C => hallvars B ++ hallvars C
| hfrl x B => x :: hallvars B
| hexs x B => x :: hallvars B
end.

Lemma hffreevars_hallvars : forall A, incl (hffreevars A) (hallvars A).
Proof. hformula_induction A.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  eapply incl_tran; [ apply incl_remove | ].
  eapply incl_tran; [ apply IHA | intuition ].
Qed.

Lemma hbisubs : forall x y A, ~ In x (hallvars A) ->
  hfsubs x (hvar y) (hfsubs y (hvar x) A) = A.
Proof. hformula_induction A; f_equal.
- apply htbisubs.
  intros Hin; apply H; simpl; intuition.
- apply H; simpl; intuition.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  repeat case_analysis; intuition.
  apply nfree_hfsubs.
  intros Hin; apply H1.
  now apply hffreevars_hallvars.
Qed.


(* Proofs *)
Inductive hprove : hformula -> Type :=
| hprove_K : forall A B, hprove (A ⟶ B ⟶ A)
| hprove_S : forall A B C, hprove ((A ⟶ B ⟶ C) ⟶ ((A ⟶ B) ⟶ A ⟶ C))
| hprove_MP : forall A B, hprove (A ⟶ B) -> hprove A -> hprove B
| hprove_INST : forall x A t, Forall (fun y => hgood_for x y A) (hfreevars t) ->
                   hprove (hfrl x A ⟶ hfsubs x t A)
| hprove_FRL : forall x A B, ~ In x (hffreevars A) -> hprove ((hfrl x (A ⟶ B)) ⟶ A ⟶ hfrl x B)
| hprove_GEN : forall x A, hprove A -> hprove (hfrl x A)
| hprove_EINST : forall x A t, Forall (fun y => hgood_for x y A) (hfreevars t) ->
                   hprove (hfsubs x t A ⟶ hexs x A)
| hprove_EXS : forall x A B, ~ In x (hffreevars B) -> hprove (hfrl x (A ⟶ B) ⟶ hexs x A ⟶ B).

Lemma hprove_I A : hprove (A ⟶ A).
Proof. (* I = (S K) K *)
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K with (B := A ⟶ A).
- apply hprove_K.
Qed.

Lemma hprove_B A B C : hprove ((B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶ C).
Proof. (* B = (S (K S)) K *)
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + eapply hprove_MP.
    * apply hprove_K.
    * apply hprove_S.
- apply hprove_K.
Qed.

Lemma hprove_C A B C : hprove ((A ⟶ B ⟶ C) ⟶ B ⟶ A ⟶ C).
Proof. (* C = (S ((S (K B)) S)) (K K) *)
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + eapply hprove_MP.
    * eapply hprove_MP.
      -- apply hprove_S.
      -- eapply hprove_MP.
         ++ apply hprove_K.
         ++ apply hprove_B.
    * apply hprove_S.
- eapply hprove_MP.
  + apply hprove_K.
  + apply hprove_K.
Qed.

Lemma hprove_W A B : hprove ((A ⟶ A ⟶ B) ⟶ A ⟶ B).
Proof. (* (S S) (S K) *)
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_S.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K.
Qed.

Lemma hprove_CUT B A C : hprove (A ⟶ B) -> hprove (B ⟶ C) -> hprove (A ⟶ C).
Proof. (* fun x y => (B y) x *)
intros pi1 pi2.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_B.
  + apply pi2.
- apply pi1.
Qed.

Lemma hprove_B2 A B C : hprove ((A ⟶ B) ⟶ (B ⟶ C) ⟶ A ⟶ C).
Proof. (* C B *)
eapply hprove_MP.
- apply hprove_C.
- apply hprove_B.
Qed.

End Formulas.

