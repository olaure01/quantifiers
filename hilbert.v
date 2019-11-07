(* Hilbert system for Intuitionistic Logic with implication *)

Require Import List.

Require Import stdlib_more.

Require Import atom.


Set Implicit Arguments.



(** * First-Order Terms *)

Section Terms.

Context { vatom : Atom } { tatom : Type }.

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
  (try intros until t) ;
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  apply (hterm_ind_list_Forall t) ;
  [ intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ;
    repeat (rewrite flat_map_concat_map) ; repeat (rewrite map_map) ;
    try f_equal ;
    try (apply map_ext_in ; intros i Hi; specialize_Forall_all i) ;
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i) ;
    try assumption ] ;
  try ((rnow idtac) ; fail) ; try (rcauto ; fail).

(** * Term substitutions *)

(** substitutes [term] [u] for variable [x] in [term] [t] *)
Fixpoint htsubs x u t :=
match t with
| hvar y => if eqb_at y x then u else hvar y
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
Proof. intros t x Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve hclosed_nohfreevars : term_db.

Lemma nfree_htsubs : forall x u t, ~ In x (hfreevars t) -> htsubs x u t = t.
Proof. hterm_induction t; intros Hin.
f_equal.
rewrite <- (map_id l) at 2.
apply map_ext_in; intros v Hv.
apply Forall_forall with (x:=v) in IHl; [ | assumption ].
apply IHl.
intros Hinx; apply Hin.
rewrite <- flat_map_concat_map; apply in_flat_map; exists v; split; assumption.
Qed.
Hint Rewrite nfree_htsubs using try (intuition ; fail) ;
                               (try apply hclosed_nohfreevars) ; intuition ; fail : term_db.

Lemma htsubs_htsubs_com : forall x v y u, x <> y -> ~ In x (hfreevars u) -> forall t,
  htsubs y u (htsubs x v t) = htsubs x (htsubs y u v) (htsubs y u t).
Proof. hterm_induction t. Qed.
Hint Rewrite htsubs_htsubs_com using try (intuition ; fail) ;
                                    (try apply hclosed_nohfreevars) ; intuition ; fail : term_db.

Lemma hfreevars_tsubs_closed : forall x u, hclosed u -> forall t,
  hfreevars (htsubs x u t) = remove eq_at_dec x (hfreevars t).
Proof. hterm_induction t.
revert IHl; induction l; simpl; intros Hl; [ reflexivity | ].
inversion Hl; subst.
rewrite IHl; simpl; [ | assumption ].
now rewrite remove_app; f_equal.
Qed.

Lemma hfreevars_tsubs : forall x y u t, In x (hfreevars (htsubs y u t)) ->
  (In x (hfreevars u) /\ In y (hfreevars t)) \/ (In x (hfreevars t) /\ x <> y).
Proof.
hterm_induction t.
- case eq_at_reflect; intros Heq Hin; auto.
  simpl in Hin; destruct Hin; auto; subst.
  right; split; auto.
- revert IHl; induction l; simpl; intros Hl Hin.
  + inversion Hin.
  + inversion Hl; subst.
    apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    * apply H1 in Hin.
      destruct Hin as [Hin|Hin]; [left|right].
      -- destruct Hin; split; auto.
         apply in_or_app; auto.
      -- split.
         ++ now apply in_or_app; left.
         ++ destruct Hin; auto.
    * apply IHl in H2; auto.
      destruct H2 as [H2|H2]; [left|right].
      -- destruct H2; split; auto.
         apply in_or_app; auto.
      -- split.
         ++ now apply in_or_app; right.
         ++ destruct H2; auto.
Qed.

Lemma hfreevars_to_tsubs : forall t a x u,
  In x (hfreevars t) -> In a (hfreevars u) -> In a (hfreevars (htsubs x u t)).
Proof. hterm_induction t; intros a y u Hin1 Hin2.
- destruct Hin1 as [Hin1|Hin1]; [ | inversion Hin1 ]; subst.
  now rewrite eqb_refl.
- revert IHl Hin1; induction l; simpl; intros Hl Hin; [ inversion Hin | ].
  inversion Hl; subst.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [ left | right ].
  + now apply H1.
  + now apply IHl.
Qed.

Lemma htbisubs : forall x y t, ~ In x (hfreevars t) ->
  htsubs x (hvar y) (htsubs y (hvar x) t) = t.
Proof. hterm_induction t; intros Hin.
f_equal.
rewrite <- (map_id l) at 2.
apply map_ext_in; intros z Hz.
apply Forall_forall with (x:=z) in IHl; auto.
apply IHl.
intros Hin2; apply Hin.
revert Hz; clear - Hin2; induction l; intros Hin; inversion Hin; subst.
- now simpl; apply in_or_app; left.
- apply IHl in H.
  now simpl; apply in_or_app; right.
Qed.

End Terms.



(* Formulas and Proofs *)

Section Formulas.

Context { vatom : Atom } { tatom : Type } { fatom : Type }.
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
  induction A as [ XX ll | A1 A2 | xx A | xx A ] ; simpl ; intros ;
  [ rewrite ? flat_map_concat_map;
    try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; intuition ;
                       rewrite IHll ; f_equal ; intuition)
  | try (f_equal ; intuition)
  | try (repeat case_analysis; intuition; f_equal ; intuition; (rnow idtac); fail)
  | try (repeat case_analysis; intuition; f_equal ; intuition; (rnow idtac); fail) ];
  try ((rnow idtac) ; fail) ; try (rcauto ; fail).


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
| hfrl x B => remove eq_at_dec x (hffreevars B)
| hexs x B => remove eq_at_dec x (hffreevars B)
end.

Fixpoint hgood_for x y A :=
match A with
| hfvar X l => True
| himp B C => hgood_for x y B /\ hgood_for x y C
| hfrl z B => In x (hffreevars (hfrl z B)) -> (hgood_for x y B /\ y <> z)
| hexs z B => In x (hffreevars (hexs z B)) -> (hgood_for x y B /\ y <> z)
end.

(** substitutes [hterm] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint hfsubs x u A :=
match A with
| hfvar X l => hfvar X (map (htsubs x u) l)
| himp B C => himp (hfsubs x u B) (hfsubs x u C)
| hfrl y B => hfrl y (if eqb_at y x then B else hfsubs x u B)
| hexs y B => hexs y (if eqb_at y x then B else hfsubs x u B)
end.

Lemma hfsize_subs : forall u x A, hfsize (hfsubs x u A) = hfsize A.
Proof. hformula_induction A; case eq_at_reflect; intros; auto. Qed.
Hint Rewrite hfsize_subs : term_db.

Lemma nfree_hfsubs : forall x u A, ~ In x (hffreevars A) -> hfsubs x u A = A.
Proof. hformula_induction A; try rcauto.
- apply nfree_htsubs.
  intros  Hin; apply H.
  now apply in_or_app; left.
- apply H.
  now apply in_or_app; right.
- f_equal; apply IHA.
  intros Hin; apply H.
  apply notin_remove; [ | assumption ].
  intros ?; auto.
- f_equal; apply IHA.
  intros Hin; apply H.
  apply notin_remove; [ | assumption ].
  intros ?; auto.
Qed.

Lemma hffreevars_subs : forall x y u A, In x (hffreevars (hfsubs y u A)) ->
  (In x (hfreevars u) /\ In y (hffreevars A)) \/ (In x (hffreevars A) /\ x <> y).
Proof. hformula_induction A.
- revert H; induction l; simpl; intros Hin; [ now idtac | ].
  apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  + apply hfreevars_tsubs in Hin; destruct Hin as [Hin|Hin]; [left|right]; destruct Hin; split; auto.
    * now apply in_or_app; left.
    * now apply in_or_app; left.
  + apply IHl in Hin; destruct Hin as [Hin|Hin]; [left|right]; destruct Hin; split; auto.
    * now apply in_or_app; right.
    * now apply in_or_app; right.
- apply in_app_or in H; destruct H as [H|H].
  + apply A1 in H; destruct H as [H|H]; [left|right]; destruct H; split; auto.
    * now apply in_or_app; left.
    * now apply in_or_app; left.
  + apply IHA1 in H; destruct H as [H|H]; [left|right]; destruct H; split; auto.
    * now apply in_or_app; right.
    * now apply in_or_app; right.
- revert H; case eq_at_reflect; intros Heq Hin.
  + right; subst.
    simpl in Hin; apply in_remove in Hin; destruct Hin; split; auto.
    now apply notin_remove.
  + simpl in Hin; apply in_remove in Hin; destruct Hin as [Hin Hneq].
    apply IHA in Hin; destruct Hin as [Hin|Hin]; [left|right]; destruct Hin; split; auto.
    * apply notin_remove; auto.
    * now apply notin_remove.
- revert H; case eq_at_reflect; intros Heq Hin.
  + right; subst.
    simpl in Hin; apply in_remove in Hin; destruct Hin; split; auto.
    now apply notin_remove.
  + simpl in Hin; apply in_remove in Hin; destruct Hin as [Hin Hneq].
    apply IHA in Hin; destruct Hin as [Hin|Hin]; [left|right]; destruct Hin; split; auto.
    * apply notin_remove; auto.
    * now apply notin_remove.
Qed.

Lemma hffreevars_to_subs : forall A a x t,
  Forall (fun y => hgood_for x y A) (hfreevars t) ->
  In x (hffreevars A) -> In a (hfreevars t) -> In a (hffreevars (hfsubs x t A)).
Proof. hformula_induction A.
- revert H0 H1; clear; induction l; intros Hin1 Hin2; simpl.
  + inversion Hin1.
  + simpl in Hin1.
    apply in_or_app; apply in_app_or in Hin1; destruct Hin1 as [Hin1|Hin1]; [left|right].
    * now apply hfreevars_to_tsubs.
    * now apply IHl.
- apply Forall_and_inv in H; destruct H as [Hl Hr].
  apply in_or_app; apply in_app_or in H0; destruct H0 as [Hin|Hin]; [ left | right ].
  + now apply A1.
  + now apply IHA1.
- case eq_at_reflect; intros Heq; simpl.
  + exfalso; subst.
    now apply remove_In in H0.
  + case (eq_at_reflect a x); intros Heq2.
    * exfalso; subst.
      apply in_remove in H0.
      apply Forall_forall with (x:=x) in H; [ | assumption ].
      destruct H0.
      apply (notin_remove eq_at_dec _ x0 x) in H0.
      -- now apply H in H0.
      -- intros Heq2; now apply Heq.
    * apply notin_remove; [ assumption | ].
      apply IHA; try assumption.
      -- apply Forall_forall; intros y Hy.
         apply Forall_forall with (x:=y) in H; [ | assumption ].
         now apply H in H0.
      -- now apply in_remove in H0.
- case eq_at_reflect; intros Heq; simpl.
  + exfalso; subst.
    now apply remove_In in H0.
  + case (eq_at_reflect a x); intros Heq2.
    * exfalso; subst.
      apply in_remove in H0.
      apply Forall_forall with (x:=x) in H; [ | assumption ].
      destruct H0.
      apply (notin_remove eq_at_dec _ x0 x) in H0.
      -- now apply H in H0.
      -- intros Heq2; now apply Heq.
    * apply notin_remove; [ assumption | ].
      apply IHA; try assumption.
      -- apply Forall_forall; intros y Hy.
         apply Forall_forall with (x:=y) in H; [ | assumption ].
         now apply H in H0.
      -- now apply in_remove in H0.
Qed.

Fixpoint hallvars A :=
match A with
| hfvar _ l => concat (map hfreevars l)
| himp B C => hallvars B ++ hallvars C
| hfrl x B => x :: hallvars B
| hexs x B => x :: hallvars B
end.

Lemma hffreevars_hallvars : forall A, incl (hffreevars A) (hallvars A).
Proof.
hformula_induction A.
- intros z Hz.
  apply in_cons.
  apply in_remove in Hz; destruct Hz.
  now apply IHA.
- intros z Hz.
  apply in_cons.
  apply in_remove in Hz; destruct Hz.
  now apply IHA.
Qed.

Lemma hbisubs : forall x y A, ~ In x (hallvars A) ->
  hfsubs x (hvar y) (hfsubs y (hvar x) A) = A.
Proof. hformula_induction A.
- apply htbisubs.
  intros Hin; apply H.
  now simpl; apply in_or_app; left.
- apply H.
  now simpl; apply in_or_app; right.
- repeat case_analysis; f_equal; intuition.
  apply nfree_hfsubs.
  intros Hin; apply H1.
  now apply hffreevars_hallvars.
- repeat case_analysis; f_equal; intuition.
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
Proof.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K with (B := A ⟶ A).
- apply hprove_K.
Qed.

Lemma hprove_B A B C : hprove ((B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶ C).
Proof.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + eapply hprove_MP.
    * apply hprove_K.
    * apply hprove_S.
- apply hprove_K.
Qed.

Lemma hprove_C A B C : hprove ((A ⟶ B ⟶ C) ⟶ B ⟶ A ⟶ C).
Proof.
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
Proof.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_S.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K.
Qed.

Lemma hprove_CUT B A C : hprove (A ⟶ B) -> hprove (B ⟶ C) -> hprove (A ⟶ C).
Proof.
intros pi1 pi2.
eapply hprove_MP; [ eapply hprove_MP | ]; [ apply hprove_B | eassumption | assumption ].
Qed.

Lemma hprove_B2 A B C : hprove ((A ⟶ B) ⟶ (B ⟶ C) ⟶ A ⟶ C).
Proof. eapply hprove_MP; [ apply hprove_C | apply hprove_B ]. Qed.

End Formulas.

