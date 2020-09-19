(* From Natural Deduction to Hilbert System *)

Require Import lib_files.infinite lib_files.List_more lib_files.List_assoc.

Require Export nj1_frlexs hilbert.

Set Implicit Arguments.


Section N2H.

Context { vatom : InfDecType } { tatom fatom : Type }.

Arguments tvar {_} {_} {T} _.

Notation hterm := (@term vatom tatom Empty_set).
Notation hformula := (@formula vatom tatom fatom Nocon Icon Qcon Empty_set).

Notation term := (@term vatom tatom nat).
Notation formula := (@formula vatom tatom fatom Nocon Icon Qcon nat).
Notation closed t := (tvars t = nil).
Notation fclosed r := (forall n, closed (r n)).
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "A [[ L ]]" := (multi_subs L A) (at level 8, format "A [[ L ]]").
Notation "L ∖ x" := (remove_assoc x L) (at level 18).
Notation "⇑" := fup.
Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "l ⇈" := (map (fun F => F↑) l) (at level 8, format "l ⇈").
Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "x ∉ A" := (~ In x (freevars A)) (at level 30).
Notation "y #[ x ] A" := (no_capture_at x y A) (at level 30, format "y  #[ x ]  A").
Notation "r #[[ l ]] A" := (no_ecapture_at r l A) (at level 30, format "r  #[[ l ]]  A").

Infix "→" := (fbin imp_con) (at level 55, right associativity).

Hint Resolve no_ecapture_not_egenerated : term_db.


Section Fixed_r.

Variable r : nat -> hterm.

Notation n2h_term := (tesubs r).
Notation n2h_formula := (esubs r).

(* Turn sequents into formulas *)
Definition s2f l (A : formula) := fold_left (fun x y => y → x) l A.

Lemma no_ecapture_s2f : forall lv l A,
  r #[[lv]] (s2f l A) <-> Forall (no_ecapture_at r lv) (A :: l).
Proof.
induction l; simpl; intros A; split; intros Hg; intuition.
- inversion_clear Hg; intuition.
- apply IHl in Hg; inversion_clear Hg as [ | ? ? Hi Hl]; simpl in Hi; intuition.
- apply IHl; inversion_clear Hg as [ | ? ? Hi Hl]; inversion_clear Hl; constructor; simpl; intuition.
Qed.

Notation n2h_sequent l A := (n2h_formula (s2f l A)).

Lemma n2h_sequent_fvars : forall l A,
  incl (fvars (n2h_sequent l A))
       (fvars (n2h_formula A) ++ flat_map (fun C => fvars (n2h_formula C)) l).
Proof. induction l; simpl; intros A C HC; intuition; apply IHl in HC; in_solve. Qed.

Lemma hprove_Bsequent : forall l A B,
  hprove ((n2h_formula A → n2h_formula B) → n2h_sequent l A → n2h_sequent l B).
Proof.
induction l; simpl; intros A B.
- apply hprove_I.
- specialize IHl with (a → A) (a → B); simpl in IHl.
  eapply hprove_CUT; [ apply hprove_B | apply IHl ].
Qed.

Lemma hprove_K2sequent : forall l A,
  hprove (n2h_sequent (A :: l) A).
Proof.
induction l; simpl; intros A.
- apply hprove_I.
- eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_K ] | apply IHl ].
Qed.

Lemma hprove_Ksequent : forall l1 l2 A,
  hprove (n2h_sequent l1 A) -> hprove (n2h_sequent (l2 ++ l1) A).
Proof.
intros l1 l2; revert l1; induction l2; simpl; intros l1 A pi; [ assumption | ].
specialize IHl2 with l1 (a → A); apply IHl2.
eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_K ] | apply pi ].
Qed.

Lemma hprove_Ssequent : forall l A B,
  hprove (n2h_sequent l (A → B) → n2h_sequent l A → n2h_sequent l B).
Proof.
induction l; simpl; intros A B.
- apply hprove_I.
- specialize IHl with (a → A) (a → B); simpl in IHl.
  eapply hprove_CUT; [ | apply IHl ].
  eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_S ].
Qed.

Lemma hprove_sequent_imp : forall l A B,
  hprove (n2h_sequent l (A → B)) -> hprove (n2h_formula A → n2h_sequent l B).
Proof.
induction l; simpl; intros A B pi; auto.
apply IHl.
eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply pi ]; simpl.
apply hprove_C.
Qed.

Lemma hprove_imp_sequent : forall l A B,
  hprove (n2h_formula A → n2h_sequent l B) -> hprove (n2h_sequent l (A → B)).
Proof.
induction l; simpl; intros A B pi; auto.
apply IHl in pi.
eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply pi ]; simpl.
apply hprove_C.
Qed.

Lemma hprove_FRLsequent : forall x l A, ~ In x (flat_map (fun C => freevars (n2h_formula C)) l) ->
  hprove ((frl x (n2h_sequent l A)) → n2h_sequent l (frl x A)).
Proof.
induction l; simpl; intros A Hf.
- apply hprove_I.
- eapply hprove_CUT; [ apply IHl | ].
  + intros Hin; apply Hf; in_solve.
  + eapply hprove_MP; [ apply hprove_Bsequent | ]; simpl.
    apply hprove_FRL.
    intros Hin; apply Hf; in_solve.
Qed.

End Fixed_r.


Notation n2h_term := (@tesubs vatom tatom nat Empty_set).
Notation n2h_formula := (@esubs vatom tatom fatom Nocon Icon Qcon nat Empty_set).
Notation n2h_sequent r l A := (n2h_formula r (s2f l A)).
Notation no_ecapture r := (no_ecapture_at r nil).

Definition rrename x y (r : nat -> hterm) n := tsubs x (tvar y) (r n).

Lemma tvars_rrename : forall x y r n z,
  In z (tvars (rrename x y r n)) ->
    (z = y /\ In x (tvars (r n))) \/ (In z (tvars (r n)) /\ z <> x).
Proof. unfold rrename; intros x y r n z Hin; apply tvars_tsubs in Hin; simpl in Hin; in_solve. Qed.

Lemma tvars_n2h_rrename : forall x y r t z,
  In z (tvars (n2h_term (rrename x y r) t)) -> z = y \/ In z (tvars (n2h_term r t)).
Proof. term_induction t.
- intros z Hin.
  apply tvars_rrename in Hin; intuition.
- rewrite flat_map_map in H.
  apply in_flat_map in H; destruct H as [ u [Huin Hinu] ].
  specialize_Forall IHl with u; apply IHl in Hinu.
  destruct Hinu as [Hinu|Hinu]; [left; assumption | right].
  rewrite <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
Qed.

Lemma tvars_n2h_rrename_self : forall x y r t,
  no_tecapture_at r (x::nil) t -> ~ In y (tvars t) ->
  In y (tvars (n2h_term (rrename x y r) t)) -> In y (tvars (n2h_term r t)).
Proof. term_induction t.
- intros Hg Hnin Hin.
  apply tvars_rrename in Hin; destruct Hin as [Hin|Hin]; intuition.
  inversion_clear Hg; intuition.
- apply Forall_fold_right in H.
  rewrite flat_map_map in H1; apply in_flat_map in H1; destruct H1 as [ u [Huin Hinu] ].
  specialize_Forall_all u; apply IHl in H; intuition.
  + rewrite <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
  + apply H0, in_flat_map; exists u; intuition.
Qed.

Lemma freevars_n2h_rrename_self : forall x y r A,
  r #[[x::nil]] A -> y ∉ A ->
  y ∈ (n2h_formula (rrename x y r) A) -> y ∈ (n2h_formula r A).
Proof. formula_induction A.
- apply Forall_fold_right in H.
  rewrite flat_map_map in H1; apply in_flat_map in H1; destruct H1 as [ u [Huin Hinu] ].
  specialize_Forall_all u.
  apply tvars_n2h_rrename_self in Hinu; intuition.
  + rewrite map_map, <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
  + apply H0, in_flat_map; exists u; intuition.
- apply in_or_app; apply in_app_or in H1; destruct H1 as [Hin|Hin]; [left|right]; intuition.
- apply in_remove in H1; destruct H1 as [Hin Hneq]; apply in_in_remove; intuition.
  apply IHA; intuition.
  + apply no_ecapture_less with (lv1:= x::nil) in H; [ intuition | in_solve ].
  + apply H0, in_in_remove; intuition.
Qed.

Lemma fvars_n2h_rrename : forall x y r A z,
  In z (fvars (n2h_formula (rrename x y r) A)) -> z = y \/ In z (fvars (n2h_formula r A)).
Proof. formula_induction A.
- rewrite flat_map_map in H.
  apply in_flat_map in H; destruct H as [ u [Huin Hinu] ].
  apply tvars_n2h_rrename in Hinu.
  destruct Hinu as [Hinu|Hinu]; [left; intuition | right].
  rewrite map_map, <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
- apply in_app_or in H; destruct H as [Hin|Hin].
  + apply IHA1 in Hin; intuition.
  + apply IHA2 in Hin; intuition.
- intuition.
  apply IHA in H0; intuition.
Qed.

Lemma no_tecapture_rrename : forall r y x t lv, ~ In y (tvars t ++ lv) ->
  no_tecapture_at r lv t -> no_tecapture_at (rrename x y r) lv t.
Proof.
term_induction t.
- intros lv Hin Hg.
  apply Forall_forall; intros z Hz Hinz.
  specialize_Forall Hg with z; apply Hg.
  apply tvars_rrename in Hinz; intuition; subst; intuition.
- apply Forall_fold_right; apply Forall_fold_right in H0.
  apply Forall_forall; intros u Hu.
  specialize_Forall_all u.
  apply IHl; intuition.
  apply in_map with (f:= tvars( T:=nat)) in Hu.
  apply H.
  apply in_or_app; apply in_app_or in H1; destruct H1 as [H1|H1]; [left|right]; intuition.
  rewrite flat_map_concat_map.
  apply in_concat.
  now exists (tvars u).
Qed.

Lemma no_ecapture_rrename : forall r y x (A : formula) lv, ~ In y (fvars A ++ lv) ->
  r #[[lv]] A -> (rrename x y r) #[[lv]] A.
Proof. formula_induction A.
- apply Forall_fold_right in H0; apply Forall_fold_right.
  apply Forall_forall; intros u Hu.
  specialize_Forall H0 with u.
  apply no_tecapture_rrename; intuition.
  apply H.
  apply in_or_app; apply in_app_or in H1; destruct H1 as [H1|H1]; [left|right]; intuition.
  now apply in_flat_map; exists u.
- apply IHA1; intuition.
  apply H; in_solve.
- apply IHA2; intuition.
  apply H; in_solve.
- apply IHA; intuition.
  apply in_app_or in H1; destruct H1 as [H1|H1]; try inversion H1; intuition; in_solve.
Qed.


(* Freshness function now required *)

(* update [r] by refreshing all variables from [l] in the target *)
(* generated variables are moreover chosen fresh with respect to [ld] *)
Fixpoint rrefresh l ld r :=
match l with
| nil => r
| x :: tl => let y := fresh (l ++ ld) in rrefresh tl (x :: y :: ld) (rrename x y r)
end.

Lemma tvars_rrefresh : forall n l ld r z,
  In z (l ++ ld) -> In z (tvars (rrefresh l ld r n)) -> In z (tvars (r n)).
Proof.
induction l; intros ld r z Hinz Hin; simpl in Hin; auto.
apply IHl in Hin; intuition; try in_solve.
apply tvars_rrename in Hin; destruct Hin as [Hin|Hin]; intuition.
exfalso; subst.
apply fresh_prop with (a :: l ++ ld); in_solve.
Qed.

Lemma rrefresh_notin : forall n z lvA lv r,
  In z (tvars (rrefresh lvA lv r n)) -> ~ In z lvA.
Proof.
induction lvA; simpl; intros lv r Hinf Hin; inversion Hin; subst; simpl in Hin.
- apply tvars_rrefresh in Hinf; try in_solve.
  apply tvars_rrename in Hinf; destruct Hinf as [ [Hinf _] | Hinf ]; [ | intuition ].
  apply fresh_prop with (z :: lvA ++ lv); rewrite <- Hinf; now constructor.
- now apply IHlvA in Hinf.
Qed.

Lemma no_ecapture_rrefresh_preserv : forall l r ld lv (A : formula), incl (fvars A ++ lv) ld ->
  r #[[lv]] A -> (rrefresh l ld r) #[[lv]] A.
Proof.
induction l; intros r ld lv A Hld Hg; simpl; auto.
apply IHl; try (intros; in_solve).
apply no_ecapture_rrename; auto; intros Hin.
apply fresh_prop with (a :: l ++ ld).
apply Hld in Hin; in_solve.
Qed.

Lemma no_tecapture_rrefresh : forall ld t r lvt lv, incl (tvars (n2h_term r t) ++ lv) lvt ->
  no_tecapture_at (rrefresh lvt ld r) lv t.
Proof. term_induction t.
- intros r lvt lv Hincl.
  apply Forall_forall; intros z Hz Hinz.
  apply rrefresh_notin in Hinz; apply Hinz; in_solve.
- apply Forall_fold_right.
  apply Forall_forall; intros u Hu.
  specialize_Forall IHl with u; apply IHl.
  intros z Hz; apply H.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; intuition.
  apply in_map with (f:= fun x => tvars (n2h_term r x)) in Hu.
  now rewrite flat_map_concat_map, map_map; apply in_flat_map; exists (tvars (n2h_term r u)).
Qed.

Lemma no_ecapture_rrefresh : forall ld A r lvA lv,
  incl (fvars (n2h_formula r A) ++ lv) lvA -> (rrefresh lvA ld r) #[[lv]] A.
Proof. formula_induction A; 
  (try apply IHA1); (try apply IHA2); (try apply IHA); try (intros z Hz; apply H; in_solve).
apply Forall_fold_right.
apply Forall_forall; intros u Hu.
apply no_tecapture_rrefresh.
intros z Hz; apply H.
apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; intuition.
apply in_map with (f:= fun x => tvars (n2h_term r x)) in Hu.
rewrite flat_map_concat_map, map_map; apply in_flat_map; exists (tvars (n2h_term r u)); intuition.
Qed.
Arguments no_ecapture_rrefresh : clear implicits.

Lemma bitrename : forall r y x t,
  ~ In y (tvars t ++ tvars (n2h_term r t)) ->
  tsubs y (tvar x) (n2h_term (rrename x y r) t) = n2h_term r t.
Proof. term_induction t.
- intros Hnin.
  now unfold rrename; apply notin_tsubs_bivar.
- apply IHl; intros Hnin; apply H.
  apply in_or_app; apply in_app_or in Hnin; destruct Hnin as [Hin|Hin]; [left|right].
  + now apply in_flat_map; exists i.
  + apply in_map with (f:= n2h_term r) in Hi.
    now apply in_flat_map; exists (n2h_term r i).
Qed.

Lemma birename : forall r y x A,
  ~ In y (fvars A ++ freevars (n2h_formula r A)) ->
  (n2h_formula (rrename x y r) A)[tvar x//y] = n2h_formula r A.
Proof. formula_induction A.
- apply bitrename; intros Hin; apply H; in_solve.
- apply H; in_solve.
- apply IHA1; intros Hin; apply H; in_solve.
- apply IHA2; intros Hin; apply H; in_solve.
- apply IHA; intros Hin; apply H; right.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition.
  apply in_in_remove; intuition.
Qed.

Lemma hrrename : forall r y x A,
  ~ In y (fvars A ++ freevars (n2h_formula r A)) -> no_ecapture r A ->
  hprove (n2h_formula (rrename x y r) A) -> hprove (n2h_formula r A).
Proof.
intros r y x A Hnin Hg pi.
rewrite <- birename with (x:=x) (y:=y); auto.
eapply hprove_MP; [ apply hprove_INST | apply hprove_GEN ]; auto.
simpl; repeat constructor.
revert Hnin Hg; clear; formula_induction A.
- apply IHA1; intuition; apply Hnin; in_solve.
- apply IHA2; intuition; apply Hnin; in_solve.
- split.
  + apply IHA; intuition.
    * apply H2.
      apply in_or_app; apply in_app_or in H0; destruct H0 as [Hin|Hin]; [left|right]; intuition.
      apply in_in_remove; intuition.
    * apply no_ecapture_less with (lv1:=nil) in Hg; [ intuition | in_solve ].
  + intros Heq; subst.
    apply Hnin; right.
    apply in_or_app; right.
    apply in_remove in H; destruct H as [Hin Hneq]; apply in_in_remove; intuition.
    apply freevars_n2h_rrename_self in Hin; intuition.
    apply H0, in_or_app; left.
    now apply freevars_fvars.
Qed.

Lemma hrrefresh : forall l r ld A,
  incl (fvars (n2h_formula r A)) ld -> no_ecapture r A ->
  hprove (n2h_formula (rrefresh l ld r) A) -> hprove (n2h_formula r A).
Proof.
induction l; intros r ld A HA Hg pi; simpl; auto.
apply IHl in pi.
- apply hrrename in pi; auto.
  intros Hin.
  apply fresh_prop with (a :: l ++ ld).
  assert (Hincl := fvars_esubs r A).
  apply Hincl, HA in Hin; in_solve.
- intros z Hz.
  apply fvars_n2h_rrename in Hz; intuition; subst; intuition.
- apply no_ecapture_rrename; auto.
  rewrite app_nil_r; intros Hin.
  apply fresh_prop with (a :: l ++ ld).
  assert (Ha := fvars_esubs r A).
  eapply or_introl in Hin; apply in_or_app, Ha, HA in Hin; in_solve.
Qed.


Definition hfelift (u : hterm) r := fun n =>
  match n with
  | 0 => u
  | S k => r k
  end.
Notation "⇑ [ u ] r" := (hfelift u r) (at level 25, format "⇑ [ u ] r").

Lemma no_tecapture_hfelift : forall u r t lv,
  no_tecapture_at r lv t -> no_tecapture_at (⇑[u]r) lv (tesubs ⇑ t).
Proof. term_induction t.
apply Forall_fold_right in H; apply Forall_fold_right.
apply Forall_forall; intros z Hz.
apply in_map_iff in Hz; destruct Hz as [ y [Heq Hy] ]; subst.
specialize_Forall_all y; auto.
Qed.

Lemma no_ecapture_hfelift : forall u r (A : formula) lv,
  r #[[lv]] A -> (⇑[u]r) #[[lv]] A↑.
Proof. formula_induction A.
apply Forall_fold_right in H; apply Forall_fold_right.
apply Forall_forall; intros v Hv.
apply in_map_iff in Hv; destruct Hv as [ v' [Heq Hv'] ]; subst.
specialize_Forall H with v'.
now apply no_tecapture_hfelift.
Qed.

Lemma no_tecapture_hfeliftz : forall r x y lv t,
  ~ In y lv -> ~ In y (tvars (n2h_term r t)) ->
  no_tecapture_at r lv t -> no_tecapture_at (⇑[tvar y]r) lv (tsubs x (evar 0) (tesubs ⇑ t)).
Proof. term_induction t.
- intros Hlv Hy Hg.
  case_analysis; intuition.
  apply Forall_forall; intros z Hz; intros Heqz; intuition; subst; intuition.
- apply Forall_fold_right; apply Forall_fold_right in H1.
  apply Forall_forall; intros z Hz.
  apply in_map_iff in Hz; destruct Hz as [ z' [Heq Hz] ]; subst.
  specialize_Forall_all z'.
  apply IHl; intuition.
  apply H0.
  rewrite flat_map_map; apply in_flat_map; exists z'; intuition.
Qed.

Lemma no_ecapture_hfeliftz : forall r x y A lv,
  In x lv -> ~ In y lv -> ~ In y (fvars (n2h_formula r A)) ->
  r #[[lv]] A -> (⇑[tvar y]r) #[[lv]] A↑[evar 0//x].
Proof. formula_induction A;
try rename H into Hxlv; try rename H0 into Hylv; try rename H1 into Hyl; try rename H2 into Hg.
- apply Forall_fold_right in Hg; apply Forall_fold_right.
  rewrite map_map; apply Forall_forall; intros u Hu.
  apply in_map_iff in Hu; destruct Hu as [ v [Heq Hv] ]; subst.
  specialize_Forall Hg with v.
  apply no_tecapture_hfeliftz; intuition.
  apply Hyl.
  rewrite flat_map_map; apply in_flat_map; exists v; intuition.
- now apply no_ecapture_hfelift.
- apply IHA; intuition.
  apply Hylv.
  destruct H as [Hin|Hin]; subst; intuition.
Qed.

Lemma n2h_hfelift_tfup : forall t u r, n2h_term (⇑[t]r) (tesubs ⇑ u) = n2h_term r u.
Proof. term_induction u. Qed.
Hint Resolve n2h_hfelift_tfup : term_db.

Lemma n2h_hfelift_fup : forall t A r, n2h_formula (⇑[t]r) A↑ = n2h_formula r A.
Proof. formula_induction A. Qed.

Lemma n2h_hfelift_fupz : forall x t A r, r #[[x::nil]] A ->
  n2h_formula (⇑[t]r) A↑[evar 0//x] = (n2h_formula r A)[t//x].
Proof.
intros; rewrite subs_esubs.
- f_equal; apply n2h_hfelift_fup.
- now apply no_ecapture_not_egenerated, no_ecapture_hfelift.
Qed.

Lemma n2h : forall l A,
  prove l A -> forall r, Forall (no_ecapture r) (A :: l) -> hprove (n2h_sequent r l A).
Proof.
intros l A pi; induction pi; intros r Hg.
- apply hprove_Ksequent, hprove_K2sequent.
- apply IHpi.
  inversion_clear Hg as [ | ? ? Hg1 Hgl]; destruct Hg1; intuition.
- assert ({rf : _ & Forall (no_ecapture rf) (A → B :: l)
                  & hprove (n2h_sequent rf l B) -> hprove (n2h_sequent r l B)})
    as [rf Hg' Hp].
  { exists (rrefresh (fvars (n2h_formula r A))
                     (flat_map (fun C => fvars (n2h_formula r C)) (B :: l)) r).
    - constructor; simpl; [split | ].
      + apply no_ecapture_rrefresh.
        rewrite app_nil_r; apply incl_refl.
      + apply no_ecapture_rrefresh_preserv.
        * rewrite app_nil_r; intros z Hz.
          assert (Ha := fvars_esubs r B); in_solve.
        * now inversion Hg.
      + apply Forall_forall; intros C HC.
        apply no_ecapture_rrefresh_preserv.
        * rewrite app_nil_r; intros z Hz.
          assert (Ha := fvars_esubs r C).
          apply in_or_app; right.
          apply in_flat_map; exists C; intuition.
        * inversion Hg as [ | ? ? _ Hgl].
          now specialize_Forall Hgl with C.
    - apply hrrefresh.
      + apply n2h_sequent_fvars.
      + now apply no_ecapture_s2f. }
  apply Hp.
  eapply hprove_MP;
    [ eapply hprove_MP; [ apply hprove_Ssequent | apply IHpi1 ] | apply IHpi2 ]; auto.
  now inversion Hg' as [ | ? ? Hgi Hgl]; destruct Hgi; constructor.
- remember (flat_map (fun C => fvars (n2h_formula r C)) (frl x A :: l)) as lv.
  remember (fresh lv) as y.
  remember (⇑[tvar y]r) as r1.
  specialize IHpi with r1.
  assert (Forall (no_ecapture r1) (A↑[evar 0//x] :: map (esubs ⇑) l)) as pi'.
  { inversion_clear Hg as [ | ? ? Hgf Hgl ]; constructor.
    - simpl in Hgf; apply no_ecapture_hfeliftz with (x:= x) (y:= y) in Hgf; intuition.
      + apply no_ecapture_less with (lv1:=nil) in Hgf; now subst.
      + simpl in H; destruct H; intuition; subst x.
        apply fresh_prop with lv; subst lv; in_solve.
      + apply fresh_prop with lv; rewrite <- Heqy; subst lv; in_solve.
    - apply Forall_forall; intros B HB.
      apply in_map_iff in HB; destruct HB as [ C [Heq HC] ]; subst B.
      specialize_Forall Hgl with C.
      now subst r1; apply no_ecapture_hfelift. }
  apply IHpi in pi'.
  apply (hprove_GEN y) in pi'.
  assert (hprove (n2h_sequent r1 (map (esubs ⇑) l) (frl y (A↑[tvar y//x])))) as pi''.
  { eapply hprove_MP; [ apply hprove_FRLsequent | ].
    - intros Hin.
      apply fresh_prop with lv; rewrite <- Heqy; subst lv.
      rewrite flat_map_map in Hin; apply in_flat_map in Hin; destruct Hin as [ C [HCin HinC] ].
      apply freevars_fvars in HinC.
      rewrite Heqr1, n2h_hfelift_fup in HinC.
      apply in_flat_map; exists C; in_solve.
    - enough (n2h_sequent r1 (map (esubs ⇑) l) A↑[evar 0//x]
            = n2h_sequent r1 (map (esubs ⇑) l) A↑[tvar y//x]) as Heq
        by now rewrite <- Heq.
      enough (n2h_formula r1 A↑[evar 0//x] = n2h_formula r1 A↑[tvar y//x]) as HeqBC.
      { remember (A↑[evar 0//x]) as B.
        remember (A↑[tvar y//x]) as C.
        clear - HeqBC; revert B C HeqBC; induction l; simpl; intros B C HeqBC; intuition.
        apply IHl; simpl; f_equal; intuition. }
      subst r1; clear; formula_induction A; term_induction t. }
  remember (frl y A↑[tvar y//x]) as B.
  remember (frl x A) as C.
  assert (hprove (n2h_formula r1 B → n2h_formula r C)) as pi'''.
  { subst B C; clear - Hg Heqr1 Heqy Heqlv; simpl.
    eapply hprove_MP; [ apply hprove_FRL | ].
    - simpl; intros Hin.
      apply in_remove in Hin; destruct Hin as [Hin Hneq]; apply Hneq.
      inversion_clear Hg as [ | ? ? Hgx _ ]; simpl in Hgx.
      apply no_ecapture_hfelift with (u:= tvar y) in Hgx; rewrite <- Heqr1 in Hgx.
      rewrite subs_esubs in Hin; intuition.
      apply freevars_subs in Hin; simpl in Hin; intuition.
    - assert (~ In y (fvars (n2h_formula r1 A↑))) as HA.
      { intros Hin; rewrite Heqr1, n2h_hfelift_fup in Hin.
        apply fresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy; in_solve. }
      apply hprove_GEN.
      eapply hprove_CUT; [ apply hprove_INST with (t:=tvar x) | ]; simpl.
      + repeat constructor.
        revert HA; clear; formula_induction A.
        revert H; case_analysis; intros Hin.
        exfalso; apply HA.
        apply in_remove in Hin; destruct Hin as [Hin _];
          apply freevars_fvars in Hin; intuition.
      + enough ((n2h_formula r1 (esubs ⇑ A)[tvar y//x])[tvar x//y] = n2h_formula r A)
          as Heq by (rewrite Heq; apply hprove_I).
        rewrite subs_esubs; simpl; intuition; subst r1.
        * rewrite notin_subs_bivar; intuition.
          apply n2h_hfelift_fup.
        * inversion_clear Hg.
          apply no_ecapture_hfelift with (u:=tvar y) in H; intuition. }
  clear - Heqr1 pi'' pi'''.
  revert B C pi''' pi''; induction l; simpl; intros B C pBC pi.
  + eapply hprove_MP; eassumption.
  + apply IHl with (a↑ → B); intuition; simpl.
    subst r1; rewrite n2h_hfelift_fup.
    eapply hprove_MP; [ apply hprove_B | apply pBC ].
- assert ({rf : _ & Forall (no_ecapture rf) (frl x A :: l) /\ no_ecapture rf (subs x u A)
                  & hprove (n2h_sequent rf l A[u//x]) -> hprove (n2h_sequent r l A[u//x])})
    as [rf [Hg1 Hg2] Hp].
  { exists (rrefresh (fvars (n2h_formula r (frl x A)))
                     (flat_map (fun C => fvars (n2h_formula r C)) (A[u//x] :: l)) r).
    - split; [ constructor; simpl | ].
      + apply (@no_ecapture_rrefresh _ (frl x A) _ (fvars (n2h_formula r (frl x A)))).
        rewrite app_nil_r; now intros z Hz.
      + apply Forall_forall; intros C HC.
        apply (no_ecapture_rrefresh_preserv (fvars (n2h_formula r (frl x A)))).
        * rewrite app_nil_r; intros z Hz; apply in_or_app; right.
          apply in_flat_map; exists C; intuition.
          apply fvars_esubs; in_solve.
        * inversion_clear Hg as [ | ? ? _ Hgl ].
          now specialize_Forall Hgl with C.
      + apply no_ecapture_rrefresh_preserv.
        * rewrite app_nil_r; intros z Hz; apply in_or_app; left.
          apply fvars_esubs; in_solve.
        * now inversion Hg.
    - remember (subs x u A) as B.
      apply hrrefresh.
      + apply n2h_sequent_fvars.
      + now apply no_ecapture_s2f. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply IHpi ]; auto.
  rewrite subs_esubs; [ apply hprove_INST | ]; intuition.
  + inversion_clear Hg1.
    apply no_ecapture_esubs_subs_closed; intuition.
  + inversion Hg1; intuition.
- assert ({rf : _ & Forall (no_ecapture rf) (exs x A :: l) /\ no_ecapture rf A[u//x]
                  & hprove (n2h_sequent rf l (exs x A)) -> hprove (n2h_sequent r l (exs x A))})
    as [rf [Hg1 Hg2] Hp].
  { exists (rrefresh (fvars (n2h_formula r A[u//x]))
                     (flat_map (fun C => fvars (n2h_formula r C)) (exs x A :: l)) r).
    - split; [ constructor; simpl | ].
      + apply no_ecapture_rrefresh_preserv.
        * intros z Hz; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; try in_solve.
          eapply or_introl in Hz; apply in_or_app, fvars_esubs with (r0:=r) in Hz; in_solve.
        * now inversion Hg.
      + apply Forall_forall; intros C HC.
        apply (no_ecapture_rrefresh_preserv (fvars (n2h_formula r A[u//x]))).
        * rewrite app_nil_r; intros z Hz; right; apply in_or_app; right.
          apply in_flat_map; exists C; intuition.
          apply fvars_esubs; in_solve.
        * inversion_clear Hg as [ | ? ? _ Hgl ].
          now specialize_Forall Hgl with C.
      + apply (no_ecapture_rrefresh _ A[u//x] _ (fvars (n2h_formula r A[u//x]))).
        rewrite app_nil_r; now intros z Hz.
    - remember (exs x A) as B.
      apply hrrefresh.
      + apply n2h_sequent_fvars.
      + now apply no_ecapture_s2f. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply IHpi ]; auto.
  + rewrite subs_esubs; simpl; [ apply hprove_EINST | ]; intuition.
    * inversion_clear Hg1.
      apply no_ecapture_esubs_subs_closed; intuition.
    * inversion Hg1; intuition.
  + inversion Hg1; now constructor.
- remember (rrefresh (fvars (n2h_formula r (exs x A)))
                     (flat_map (fun C => fvars (n2h_formula r C)) (C :: l)) r) as r1.
  assert (Forall (no_ecapture r1) (C :: l)) as HgCl1.
  { apply Forall_forall; intros D HD.
    specialize_Forall Hg with D.
    subst r1; apply no_ecapture_rrefresh_preserv; intuition.
    rewrite app_nil_r; intros z Hz.
    apply in_flat_map; exists D; intuition.
    apply fvars_esubs; in_solve. }
  assert (no_ecapture r1 C) as HgC1 by (now inversion HgCl1).
  assert (Forall (no_ecapture r1) l) as Hgl1 by (now inversion HgCl1); clear HgCl1.
  assert (no_ecapture r1 (exs x A)) as HgA1
    by (subst; apply no_ecapture_rrefresh; rewrite app_nil_r; now intros z Hz).
  apply hrrefresh with (l:=fvars (n2h_formula r (exs x A)))
                       (ld:=flat_map (fun C => fvars (n2h_formula r C)) (C :: l)).
  + apply n2h_sequent_fvars.
  + now apply no_ecapture_s2f.
  + rewrite <- Heqr1.
    eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Ssequent | ]
                      | apply IHpi1; constructor; auto ].
    apply hprove_imp_sequent.
    remember (flat_map (fun C => fvars (n2h_formula r1 C)) (exs x A :: C :: l)) as lv.
    remember (fresh lv) as y.
    assert (hprove (exs x (n2h_formula r1 A) → exs y (n2h_formula r1 A)[tvar y//x]))
      as pi'.
    { remember (n2h_formula r1 A) as B; clear - HeqB Heqy Heqlv.
      assert (~ In y (fvars B)) as Hf
        by (intros Hin; subst B; apply fresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy;
            in_solve).
      clear - Hf; eapply hprove_MP; [ apply hprove_EXS | ].
      - simpl; intros Hin; apply Hf.
        apply in_remove in Hin; destruct Hin as [Hin _].
        apply freevars_subs in Hin; destruct Hin as [Hin|Hin]; intuition.
        simpl in H; destruct H; intuition; subst.
        now apply freevars_fvars.
      - apply hprove_GEN.
        replace (B → exs y B[tvar y//x])
           with (B[tvar y//x][tvar x//y] → exs y B[tvar y//x])
          by now rewrite notin_subs_bivar.
        apply hprove_EINST.
        simpl; repeat constructor.
        revert Hf; formula_induction B.
        revert H; case_analysis; intros Hin; apply in_remove in Hin; intuition.
        * exfalso; apply H2.
          now apply freevars_fvars.
        * apply H2.
          now apply freevars_fvars. }
    simpl; eapply hprove_CUT; [ apply pi' | ].
    eapply hprove_MP; [ apply hprove_EXS | ].
    * intros Hin.
      apply fresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy.
      simpl; right; apply in_or_app; right.
      apply n2h_sequent_fvars, fvars_esubs; in_solve.
    * apply hprove_GEN.
      replace (tvar y) with (n2h_term r1 (tvar y)) by reflexivity.
      rewrite <- subs_esubs; intuition.
      apply hprove_sequent_imp.
      remember (⇑[tvar y]r1) as r2.
      assert (Forall (no_ecapture r2) (C↑ :: A↑[evar 0//x] :: map (esubs ⇑) l)) as pi.
      { constructor; [ | constructor ]; subst r2.
        - now apply no_ecapture_hfelift.
        - simpl in HgA1; apply no_ecapture_hfeliftz with (x:=x) (y:=y) in HgA1; intuition.
          + now apply no_ecapture_less with (lv1:=nil) in HgA1.
          + simpl in H; destruct H; intuition; subst x.
            apply fresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy; now left.
          + apply fresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy; in_solve.
        - apply Forall_forall; intros E HE.
          apply in_map_iff in HE; destruct HE as [ E' [Heq HE] ]; subst E.
          specialize_Forall Hgl1 with E'.
          now apply no_ecapture_hfelift. }
      apply IHpi2 in pi; simpl in pi.
      remember (A↑[evar 0//x] → C↑) as B.
      remember (A[tvar y//x] → C) as D.
      assert (hprove (n2h_formula r2 B → n2h_formula r1 D)) as HBD.
      { subst B D r2; simpl; rewrite ? n2h_rup.
        rewrite n2h_hfelift_fupz; intuition.
        rewrite n2h_hfelift_fup; intuition.
        enough (n2h_formula r1 A[tvar y//x] = (n2h_formula r1 A)[tvar y//x])
          as Heq by (rewrite Heq; apply hprove_I).
        rewrite subs_esubs; intuition. }
      clear - Heqr2 pi HBD; revert B D pi HBD; induction l; simpl; intros B D pi HBD.
      -- eapply hprove_MP; eassumption.
      -- apply IHl with (a↑ → B); auto.
         simpl; subst.
         rewrite n2h_hfelift_fup.
         eapply hprove_MP; [ apply hprove_B | apply HBD ].
Qed.

Proposition n2h_closed : forall r, fclosed r ->
  forall A, prove nil A -> hprove (n2h_formula r A).
Proof.
intros r Hc A pi; change (n2h_formula r A) with (n2h_sequent r nil A).
now apply n2h; [ | apply Forall_forall; intros; apply fclosed_no_ecapture ].
Qed.

End N2H.
