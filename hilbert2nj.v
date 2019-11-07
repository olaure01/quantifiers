(* From Hilbert to Natural Deduction *)


Require Import stdlib_more.

Require Import nj1 hilbert.


Section H2N.

Context { vatom : Atom } { tatom : Type } { fatom : Type }.
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
  induction A as [ XX ll | A1 A2 | xx A | xx A ] ; simpl ; intros ;
  [ rewrite ? flat_map_concat_map;
    try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; intuition ;
                       rewrite IHll ; f_equal ; intuition)
  | try (f_equal ; intuition)
  | try (repeat case_analysis; intuition; f_equal ; intuition; (rnow idtac); fail)
  | try (repeat case_analysis; intuition; f_equal ; intuition; (rnow idtac); fail) ];
  try ((rnow idtac) ; fail) ; try (rcauto ; fail).

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


Fixpoint h2n_term (t : hterm) :=
match t with
| hvar x => tvar x
| hconstr f l => tconstr f (map h2n_term l)
end.


Lemma h2n_freevars : forall t, freevars (h2n_term t) = hfreevars t.
Proof. hterm_induction t. Qed.

Lemma h2n_closed : forall t, hclosed t <-> closed (h2n_term t).
Proof.
intros t; rewrite h2n_freevars; destruct (hfreevars t); simpl; split; intros Heq; try reflexivity;
  inversion Heq.
Qed.

Lemma h2n_tsubs : forall x u t,
  h2n_term (htsubs x u t) = tsubs x (h2n_term u) (h2n_term t).
Proof. hterm_induction t; rewrite <- beq_hat_vat; now case_eq (beq_hat x0 x); intros Heqb. Qed.
Hint Resolve h2n_tsubs : term_db.

Lemma h2n_tup : forall k t, tup k (h2n_term t) = h2n_term t.
Proof. hterm_induction t. Qed.
Hint Resolve h2n_tup : term_db.


Fixpoint h2n_formula A : formula :=
match A with
| hfvar X l => var X (map h2n_term l)
| himp B C => imp (h2n_formula B) (h2n_formula C)
| hfrl y B => frl y (h2n_formula B)
| hexs y B => exs y (h2n_formula B)
end.

Lemma h2n_ffreevars : forall A, ffreevars (h2n_formula A) = hffreevars A.
Proof. formula_induction A; try rewrite map_app; f_equal; try assumption; apply h2n_freevars. Qed.

Lemma h2n_fclosed : forall A, hffreevars A = nil <-> ffreevars (h2n_formula A) = nil.
Proof.
intros A; rewrite h2n_ffreevars; destruct (hffreevars A); simpl; split; intros Heq; try reflexivity;
  inversion Heq.
Qed.

Lemma h2n_fsubs : forall x u A,
  h2n_formula (hfsubs x u A) = subs x (h2n_term u) (h2n_formula A).
Proof. formula_induction A. Qed.

Lemma h2n_fup : forall k A, fup k (h2n_formula A) = h2n_formula A.
Proof. formula_induction A. Qed.



Proposition h2n : forall A, hprove A ->
  forall L, Forall (fun z => closed z) (map snd L) ->
            incl (hffreevars A) (map fst L) ->
  prove nil (multi_subs L (h2n_formula A)).
Proof.
intros A pi; induction pi; intros L Hcl Hsub;
  simpl; rewrite ? multi_subs_imp;
  remember (multi_subs L (h2n_formula A)) as AA;
  (try remember (multi_subs L (h2n_formula B)) as BB);
  (try remember (multi_subs L (h2n_formula C)) as CC);
  repeat apply impi.
- change (BB :: AA :: nil) with ((BB :: nil) ++ AA :: nil).
  apply ax.
- apply (impe BB).
  + apply (impe AA).
    * change (AA :: imp AA BB :: imp AA (imp BB CC) :: nil)
        with ((AA :: imp AA BB :: nil) ++ imp AA (imp BB CC) :: nil).
      apply ax.
    * apply ax_hd.
  + apply (impe AA).
    * change (AA :: imp AA BB :: imp AA (imp BB CC) :: nil)
        with ((AA :: nil) ++ imp AA BB :: imp AA (imp BB CC) :: nil).
      apply ax.
    * apply ax_hd.
- remember (map (fun x => (x, dvar 0 : term)) (hffreevars A)) as LA.
  remember (multi_subs (L ++ LA) (h2n_formula A)) as AAA.
  apply (impe AAA).
  + specialize IHpi1 with (L ++ LA).
    simpl in IHpi1;rewrite ? multi_subs_imp in IHpi1.
    subst AAA BB; rewrite multi_subs_ext with L (h2n_formula B) LA;
      [ | | rewrite h2n_ffreevars ]; try assumption; apply IHpi1.
    * rewrite map_app; apply Forall_app; [ assumption | subst LA ].
      remember (hffreevars A) as l; clear; induction l; simpl; now constructor.
    * rewrite map_app; apply incl_app; [ apply incl_appr | apply incl_appl ].
      -- subst LA; remember (hffreevars A) as l; clear; induction l; simpl.
         ++ apply incl_refl.
         ++ apply incl_cons; [ | now apply incl_tl ].
            now constructor.
      -- assumption.
  + subst AAA; apply IHpi2.
    * rewrite map_app; apply Forall_app; [ assumption | subst LA ].
      remember (hffreevars A) as l; clear; induction l; simpl; now constructor.
    * rewrite map_app; apply incl_appr.
      subst LA; remember (hffreevars A) as l; clear; induction l; simpl.
      -- apply incl_refl.
      -- apply incl_cons; [ | now apply incl_tl ].
         now constructor.
- rewrite multi_subs_frl.
  rewrite h2n_fsubs.
  rewrite multi_subs_subs; try assumption.
  + destruct (in_dec eq_at_dec x (ffreevars (h2n_formula A))) as [Hf|Hf].
    * apply frle; [ | apply ax_hd ].
      clear - f Hcl Hsub Hf.
      apply multi_tsubs_is_closed; [ assumption | ].
      intros a Hin.
      unfold incl in Hsub; specialize Hsub with a; simpl in Hsub.
      assert (In a (hffreevars (hfsubs x t A))) as HvA.
      { rewrite h2n_ffreevars in Hf.
        rewrite h2n_freevars in Hin.
        now apply hffreevars_to_subs. }
      now eapply or_intror in HvA; apply in_or_app in HvA; eapply Hsub in HvA.
    * assert (~ In x (ffreevars (multi_subs (remove_snd x L) (h2n_formula A)))) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_ffreevars in Hin; try assumption.
        clear - Hcl; apply Forall_forall; intros a Hin.
        apply Forall_forall with (x:=a) in Hcl; [ assumption | ].
        revert Hin; clear; induction L; simpl; intros Hin.
        - inversion Hin.
        - destruct a0; simpl; simpl in Hin.
          revert Hin; case_analysis; intros Hin.
          + now right; apply IHL.
          + inversion Hin as [Hin'|Hin']; simpl in Hin'.
            * now left.
            * now right; apply IHL. }
      rewrite nfree_subs by assumption.
      rewrite <- (nfree_subs _ (dvar 0) _ Hnin).
      apply frle; [ reflexivity | ].
      rewrite nfree_subs by assumption.
      apply ax_hd.
  + apply Forall_forall; intros z Hinz.
    apply Forall_forall with (x:=z) in f.
    * revert f; clear; formula_induction A; split.
      -- apply IHA.
         apply f.
         now rewrite <- h2n_ffreevars.
      -- apply f.
         now rewrite <- h2n_ffreevars.
      -- apply IHA.
         apply f.
         now rewrite <- h2n_ffreevars.
      -- apply f.
         now rewrite <- h2n_ffreevars.
    * now rewrite <- h2n_freevars.
- rewrite ? multi_subs_frl.
  rewrite <- @multi_subs_remove with (x:=x) in HeqAA; try assumption.
  + apply frli; simpl.
    apply impe with (fup 0 AA); [ | apply ax_hd ].
    rewrite multi_subs_imp; simpl; rewrite <- HeqAA.
    replace (imp (fup 0 AA) (subs x (dvar 0)
                                (fup 0 (multi_subs (remove_snd x L) (h2n_formula B)))))
       with (imp (subs x (dvar 0) (fup 0 AA))
                           (subs x (dvar 0)
                                 (fup 0 (multi_subs (remove_snd x L) (h2n_formula B))))).
    2:{ f_equal.
        enough (~ In x (ffreevars (fup 0 AA))) as Hf by now apply nfree_subs.
        intros Hin; apply n; clear - Hcl HeqAA Hin.
        rewrite ffreevars_fup in Hin; subst.
        apply multi_subs_ffreevars in Hin.
        - now rewrite <- h2n_ffreevars.
        - revert Hcl; clear; induction L; simpl; intros Hcl; [ constructor | ].
          destruct a; simpl; simpl in Hcl; inversion Hcl; subst.
          case_analysis; intuition. }
    change (imp (subs x (dvar 0) (fup 0 AA))
                (subs x (dvar 0)
                      (fup 0 (multi_subs (remove_snd x L) (h2n_formula B)))))
      with (subs x (dvar 0) (imp (fup 0 AA)
                      (fup 0 (multi_subs (remove_snd x L) (h2n_formula B))))).
    apply frle; [ reflexivity | ].
    change (fup 0 AA :: frl x
              (imp (fup 0 AA) (fup 0 (multi_subs (remove_snd x L) (h2n_formula B)))) :: nil)
      with ((fup 0 AA :: nil) ++ frl x
              (imp (fup 0 AA) (fup 0 (multi_subs (remove_snd x L) (h2n_formula B)))) :: nil).
    apply ax.
  + intros Hin; apply n; clear - Hin.
    now rewrite h2n_ffreevars in Hin.
- rewrite multi_subs_frl.
  apply frli; simpl.
  rewrite fup_multi_subs.
  rewrite h2n_fup.
  replace (subs x (dvar 0)
          (multi_subs (map (fun x0=> (fst x0, tup 0 (snd x0))) (remove_snd x L))
             (h2n_formula A)))
     with (multi_subs ((map (fun x0 => (fst x0, tup 0 (snd x0))) (remove_snd x L) ++
             (x, dvar 0) :: nil)) (h2n_formula A))
    by now unfold multi_subs; rewrite fold_left_app; simpl.
  apply IHpi.
  + rewrite map_app; apply Forall_app.
    * rewrite map_map; simpl.
      revert Hcl; clear; induction L; simpl; intros HF; [ now constructor | ].
      inversion HF; subst.
      destruct a; simpl; simpl in H1.
      case_analysis; intuition.
      constructor; [ | now apply H ].
      now rewrite freevars_tup.
    * now repeat constructor.
  + clear - Hsub; simpl in Hsub.
    intros a Hin.
    rewrite map_app; apply in_or_app; simpl.
    case (eq_at_reflect x a); intros Heq; subst; [ right | left ]; simpl; intuition.
    unfold incl in Hsub; specialize Hsub with a.
    apply notin_remove with eq_at_dec _ _ x in Hin; [ | intuition ].
    apply Hsub in Hin.
    rewrite map_map; simpl.
    apply notin_remove with eq_at_dec _ _ x in Hin; [ | intuition ].
    now rewrite remove_snd_remove in Hin.
- rewrite multi_subs_exs.
  rewrite h2n_fsubs.
  rewrite multi_subs_subs; try assumption.
  + destruct (in_dec eq_at_dec x (ffreevars (h2n_formula A))) as [Hf|Hf].
    * eapply exsi; [ | apply ax_hd ].
      clear - f Hcl Hsub Hf.
      apply multi_tsubs_is_closed; [ assumption | ].
      intros a Hin.
      unfold incl in Hsub; specialize Hsub with a; simpl in Hsub.
      assert (In a (hffreevars (hfsubs x t A))) as HvA.
      { rewrite h2n_ffreevars in Hf.
        rewrite h2n_freevars in Hin.
        now apply hffreevars_to_subs. }
      now eapply or_introl in HvA; apply in_or_app in HvA; eapply Hsub in HvA.
    * assert (~ In x (ffreevars (multi_subs (remove_snd x L) (h2n_formula A)))) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_ffreevars in Hin; try assumption.
        clear - Hcl; apply Forall_forall; intros a Hin.
        apply Forall_forall with (x:=a) in Hcl; [ assumption | ].
        revert Hin; clear; induction L; simpl; intros Hin.
        - inversion Hin.
        - destruct a0; simpl; simpl in Hin.
          revert Hin; case_analysis; intros Hin; intuition. }
      rewrite nfree_subs by assumption.
      apply exsi with (dvar 0); [ reflexivity | ].
      rewrite nfree_subs by assumption.
      apply ax_hd.
  + apply Forall_forall; intros z Hinz.
    apply Forall_forall with (x:=z) in f.
    * revert f; clear; formula_induction A; split.
      -- apply IHA.
         apply f.
         now rewrite <- h2n_ffreevars.
      -- apply f.
         now rewrite <- h2n_ffreevars.
      -- apply IHA.
         apply f.
         now rewrite <- h2n_ffreevars.
      -- apply f.
         now rewrite <- h2n_ffreevars.
    * now rewrite <- h2n_freevars.
- rewrite multi_subs_frl.
  rewrite multi_subs_exs.
  rewrite <- @multi_subs_remove with (x:=x) in HeqBB; try assumption.
  + apply @exse with (x:=x) (A:=multi_subs (remove_snd x L) (h2n_formula A)); [ apply ax_hd | ].
    apply impe with (subs x (dvar 0) (fup 0 (multi_subs (remove_snd x L) (h2n_formula A)))); [ | apply ax_hd ].
    replace (imp (subs x (dvar 0) (fup 0 (multi_subs (remove_snd x L) (h2n_formula A)))) (fup 0 BB))
       with (subs x (dvar 0) (imp (fup 0 (multi_subs (remove_snd x L) (h2n_formula A))) (fup 0 BB))).
    2:{ simpl; f_equal.
        enough (~ In x (ffreevars (fup 0 BB))) as Hf by now apply nfree_subs.
        intros Hin; apply n; clear - Hcl HeqBB Hin.
        rewrite ffreevars_fup in Hin; subst.
        apply multi_subs_ffreevars in Hin.
        - now rewrite <- h2n_ffreevars.
        - revert Hcl; clear; induction L; simpl; intros Hcl; [ constructor | ].
          destruct a; simpl; simpl in Hcl; inversion Hcl; subst.
          case_analysis; intuition. }
    apply frle; [ reflexivity | ]; simpl.
    change (subs x (dvar 0) (fup 0 (multi_subs (remove_snd x L) (h2n_formula A)))
             :: exs x (fup 0 (multi_subs (remove_snd x L) (h2n_formula A)))
             :: frl x (fup 0 (multi_subs (remove_snd x L) (imp (h2n_formula A) (h2n_formula B)))) :: nil)
      with ((subs x (dvar 0) (fup 0 (multi_subs (remove_snd x L) (h2n_formula A)))
             :: exs x (fup 0 (multi_subs (remove_snd x L) (h2n_formula A))) :: nil)
             ++ frl x (fup 0 (multi_subs (remove_snd x L) (imp (h2n_formula A) (h2n_formula B)))) :: nil).
    rewrite multi_subs_imp; subst.
    apply ax.
  + intros Hin; apply n; clear - Hin.
    now rewrite h2n_ffreevars in Hin.
Qed.

End H2N.

