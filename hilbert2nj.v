(* From Hilbert System to Natural Deduction *)

Require Import stdlib_more.
Require Import nj1 hilbert.


Section H2N.

Context { vatom : DecType } { tatom : Type } { fatom : Type }.
Notation term := (@term vatom tatom).
Notation closed t := (freevars t = nil).
Notation tup := (@tup vatom tatom).
Notation hterm := (@hterm vatom tatom).
Notation hclosed t := (hfreevars t = nil).
Notation formula := (@formula vatom tatom fatom).
Notation hformula := (@hformula vatom tatom fatom).

Hint Rewrite
  (@tup_tup_com vatom tatom) (@tup_tsubs_com vatom tatom)
  (@ntsubs_tup_com vatom tatom) (@ntsubs_z_tup vatom tatom)
  (@freevars_tup vatom tatom) (@tsubs_tsubs_eq vatom tatom) : term_db.
Hint Resolve (@closed_nofreevars vatom tatom) : term_db.
Hint Rewrite (@freevars_ntsubs vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@nfree_tsubs vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@ntsubs_tsubs_com vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@tsubs_tsubs_com vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@freevars_tsubs_closed vatom tatom)
  using intuition; fail : term_db.

Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | A1 ? A2 ? | xx A | xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try f_equal; try (induction ll as [ | tt lll IHll ]; simpl; intuition;
                      rewrite IHll; f_equal; intuition)
  | try (f_equal; intuition)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail) ];
  try (now (rnow idtac)); try (now rcauto).

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

Ltac run_ax :=
  match goal with
  | |- prove (?l1 ++ ?B :: ?l2) ?A => (try now apply ax);
         rewrite <- (app_nil_l l2); rewrite app_comm_cons, app_assoc; run_ax
  end.
Ltac auto_ax := rewrite <- (app_nil_l _); run_ax.



Fixpoint h2n_term (t : hterm) :=
match t with
| hvar x => tvar x
| hconstr f l => tconstr f (map h2n_term l)
end.

Lemma h2n_freevars : forall t, freevars (h2n_term t) = hfreevars t.
Proof. hterm_induction t. Qed.

Lemma h2n_closed : forall t, hclosed t <-> closed (h2n_term t).
Proof. intros t; rewrite h2n_freevars; intuition. Qed.

Lemma h2n_tsubs : forall x u t,
  h2n_term (htsubs x u t) = tsubs x (h2n_term u) (h2n_term t).
Proof. hterm_induction t. Qed.
Hint Rewrite h2n_tsubs : term_db.

Lemma h2n_tup : forall k t, tup k (h2n_term t) = h2n_term t.
Proof. hterm_induction t. Qed.
Hint Rewrite h2n_tup : term_db.


Fixpoint h2n_formula A : formula :=
match A with
| hfvar X l => var X (map h2n_term l)
| himp B C => imp (h2n_formula B) (h2n_formula C)
| hfrl y B => frl y (h2n_formula B)
| hexs y B => exs y (h2n_formula B)
end.

Lemma h2n_ffreevars : forall A, ffreevars (h2n_formula A) = hffreevars A.
Proof. formula_induction A; apply h2n_freevars. Qed.

Lemma h2n_fclosed : forall A, hffreevars A = nil <-> ffreevars (h2n_formula A) = nil.
Proof. intros A; rewrite h2n_ffreevars; intuition. Qed.

Lemma h2n_fsubs : forall x u A,
  h2n_formula (hfsubs x u A) = subs x (h2n_term u) (h2n_formula A).
Proof. formula_induction A. Qed.
Hint Rewrite h2n_fsubs : term_db.

Lemma h2n_fup : forall k A, fup k (h2n_formula A) = h2n_formula A.
Proof. formula_induction A. Qed.
Hint Rewrite h2n_fup : term_db.

Lemma h2n_good_for : forall x y A, hgood_for x y A -> good_for x y (h2n_formula A).
Proof. formula_induction A; rewrite h2n_ffreevars in H0; intuition. Qed.

Proposition h2n : forall A, hprove A ->
  forall L, Forall (fun z => closed z) (map snd L) -> incl (hffreevars A) (map fst L) ->
  prove nil (multi_subs L (h2n_formula A)).
Proof.
intros A pi; induction pi; intros L Hcl Hsub;
  simpl; rewrite ? multi_subs_imp;
  remember (multi_subs L (h2n_formula A)) as AA;
  (try remember (multi_subs L (h2n_formula B)) as BB);
  (try remember (multi_subs L (h2n_formula C)) as CC);
  repeat apply impi.
- change (BB :: AA :: nil) with ((BB :: nil) ++ AA :: nil); apply ax.
- apply (impe BB).
  + apply (impe AA).
    * change (AA :: imp AA BB :: imp AA (imp BB CC) :: nil)
        with ((AA :: imp AA BB :: nil) ++ imp AA (imp BB CC) :: nil); apply ax.
    * apply ax_hd.
  + apply (impe AA).
    * change (AA :: imp AA BB :: imp AA (imp BB CC) :: nil)
        with ((AA :: nil) ++ imp AA BB :: imp AA (imp BB CC) :: nil); apply ax.
    * apply ax_hd.
- remember (map (fun x => (x, dvar 0 : term)) (hffreevars A)) as LA.
  assert (Forall (fun z => closed z) (map snd LA)) as HcLA
    by (subst LA; remember (hffreevars A) as l; clear; induction l; simpl; intuition).
  assert (map fst LA = hffreevars A) as HfstLA
    by (subst LA; remember (hffreevars A) as l; clear; induction l; simpl; try rewrite IHl; intuition).
  remember (multi_subs (L ++ LA) (h2n_formula A)) as AAA.
  apply (impe AAA).
  + specialize IHpi1 with (L ++ LA).
    simpl in IHpi1; rewrite ? multi_subs_imp in IHpi1.
    subst AAA BB; rewrite multi_subs_ext with L (h2n_formula B) LA;
      [ apply IHpi1 | assumption | rewrite h2n_ffreevars ]; rewrite ? map_app; intuition.
    * apply Forall_app; intuition.
    * apply incl_app; [ apply incl_appr | apply incl_appl ]; intuition.
      rewrite HfstLA; apply incl_refl.
  + subst AAA; apply IHpi2; rewrite ? map_app.
    * apply Forall_app; intuition.
    * apply incl_appr; rewrite HfstLA; apply incl_refl.
- rewrite multi_subs_frl, h2n_fsubs, multi_subs_subs; intuition.
  + destruct (in_dec eq_dt_dec x (ffreevars (h2n_formula A))) as [Hf|Hf].
    * apply frle; [ | apply ax_hd ].
      clear - f Hcl Hsub Hf.
      apply multi_tsubs_is_closed; [ assumption | ].
      intros z Hinz.
      apply Hsub; simpl.
      rewrite h2n_ffreevars in Hf; rewrite h2n_freevars in Hinz.
      apply hffreevars_to_subs with (x0:= z) (t0:= t) in Hf; intuition.
      now specialize_Forall f with z.
    * assert (~ In x (ffreevars (multi_subs (remove_snd x L) (h2n_formula A)))) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_ffreevars in Hin; try assumption.
        apply Forall_incl with (map snd L); intuition.
        clear; induction L; intuition; simpl; case_analysis; intuition. }
      rewrite nfree_subs by assumption.
      rewrite <- (nfree_subs _ (dvar 0) _ Hnin).
      apply frle; [ reflexivity | ].
      rewrite nfree_subs by assumption.
      apply ax_hd.
  + apply Forall_forall; intros z Hinz.
    rewrite h2n_freevars in Hinz.
    specialize_Forall f with z.
    now apply h2n_good_for.
- rewrite ? multi_subs_frl.
  rewrite <- @multi_subs_remove with (x:=x) in HeqAA; try assumption.
  + apply frli; simpl.
    apply impe with (fup 0 AA); [ | apply ax_hd ].
    rewrite multi_subs_imp; simpl; rewrite <- HeqAA.
    replace (imp (fup 0 AA) (subs x (dvar 0)
                                (fup 0 (multi_subs (remove_snd x L) (h2n_formula B)))))
       with (subs x (dvar 0) (imp (fup 0 AA)
                                (fup 0 (multi_subs (remove_snd x L) (h2n_formula B))))).
    { apply frle; intuition; auto_ax. }
    simpl; f_equal; apply nfree_subs.
    intros Hin; apply n.
    rewrite ffreevars_fup in Hin; subst.
    apply multi_subs_ffreevars in Hin.
    * now rewrite <- h2n_ffreevars.
    * apply Forall_incl with (map snd L); intuition.
      clear; induction L; intuition; simpl; case_analysis; intuition.
  + now rewrite h2n_ffreevars.
- rewrite multi_subs_frl.
  apply frli; simpl.
  rewrite fup_multi_subs, h2n_fup.
  replace (subs x (dvar 0)
          (multi_subs (map (fun x0 => (fst x0, tup 0 (snd x0))) (remove_snd x L))
             (h2n_formula A)))
     with (multi_subs ((map (fun x0 => (fst x0, tup 0 (snd x0))) (remove_snd x L) ++
             (x, dvar 0) :: nil)) (h2n_formula A))
    by now unfold multi_subs; rewrite fold_left_app; simpl.
  apply IHpi.
  + rewrite map_app; apply Forall_app.
    * rewrite map_map; simpl; rewrite <- map_map.
      revert Hcl; clear; induction L; simpl; intros HF; [ now constructor | destruct a ].
      simpl in HF; inversion_clear HF.
      case_analysis; intuition; constructor; rcauto.
    * now repeat constructor.
  + clear - Hsub; simpl in Hsub.
    intros z Hinz.
    revert Hsub; case (eq_dt_reflect z x); intros Heq Hsub; subst; rewrite map_app; simpl; try in_solve.
    rewrite map_map; simpl; rewrite <- remove_snd_remove.
    eapply notin_remove with (y:= x) in Hinz; intuition ; apply Hsub in Hinz.
    apply notin_remove with (Hdec:= eq_dt_dec) (y:= x) in Hinz; intuition.
- rewrite multi_subs_exs, h2n_fsubs, multi_subs_subs; try assumption.
  + destruct (in_dec eq_dt_dec x (ffreevars (h2n_formula A))) as [Hf|Hf].
    * eapply exsi; [ | apply ax_hd ].
      clear - f Hcl Hsub Hf.
      apply multi_tsubs_is_closed; [ assumption | ].
      intros z Hinz.
      apply Hsub; simpl.
      rewrite h2n_ffreevars in Hf; rewrite h2n_freevars in Hinz.
      apply hffreevars_to_subs with (x0:= z) (t0:= t) in Hf; intuition.
      now specialize_Forall f with z.
    * assert (~ In x (ffreevars (multi_subs (remove_snd x L) (h2n_formula A)))) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_ffreevars in Hin; try assumption.
        apply Forall_incl with (map snd L); intuition.
        clear; induction L; intuition; simpl; case_analysis; intuition. }
      rewrite nfree_subs by assumption.
      apply exsi with (dvar 0); [ reflexivity | ].
      rewrite nfree_subs by assumption.
      apply ax_hd.
  + apply Forall_forall; intros z Hinz.
    rewrite h2n_freevars in Hinz.
    specialize_Forall f with z.
    now apply h2n_good_for.
- rewrite multi_subs_frl, multi_subs_exs.
  rewrite <- @multi_subs_remove with (x:=x) in HeqBB; try assumption.
  + apply @exse with (x:=x) (A:=multi_subs (remove_snd x L) (h2n_formula A)); [ apply ax_hd | ].
    apply impe with (subs x (dvar 0) (fup 0 (multi_subs (remove_snd x L) (h2n_formula A))));
      [ | apply ax_hd ].
    replace (imp (subs x (dvar 0) (fup 0 (multi_subs (remove_snd x L) (h2n_formula A)))) (fup 0 BB))
       with (subs x (dvar 0) (imp (fup 0 (multi_subs (remove_snd x L) (h2n_formula A))) (fup 0 BB))).
    { apply frle; [ reflexivity | simpl; rewrite multi_subs_imp; subst; auto_ax ]. }
    simpl; f_equal; apply nfree_subs.
    intros Hin; apply n.
    rewrite ffreevars_fup in Hin; subst.
    apply multi_subs_ffreevars in Hin.
    * now rewrite <- h2n_ffreevars.
    * apply Forall_incl with (map snd L); intuition.
      clear; induction L; intuition; simpl; case_analysis; intuition.
  + now rewrite h2n_ffreevars.
Qed.

End H2N.

