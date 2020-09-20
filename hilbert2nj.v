(* From Hilbert System to Natural Deduction *)

Require Import lib_files.List_more lib_files.List_assoc.

Require Export foterms_std nj1_frlexs hilbert.

Set Implicit Arguments.


Section H2N.

Context { vatom : DecType } { tatom fatom : Type }.

Arguments tvar {_} {_} {T} _.

Notation hterm := (@term vatom tatom Empty_set).
Notation hformula := (@formula vatom tatom fatom Nocon Icon Qcon Empty_set).

Notation term := (@term vatom tatom nat).
Notation formula := (@formula vatom tatom fatom Nocon Icon Qcon nat).
Notation r_h2n := (@r_empty vatom tatom nat).
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

Infix "→" := (fbin imp_con) (at level 55, right associativity).

Hint Rewrite (@tsubs_tesubs_notecap vatom tatom Empty_set nat)
                          using try (intuition; fail);
                               (try apply fclosed_no_tecapture); intuition; fail : term_db.

Hint Resolve fclosed_r_empty : term_db.
Hint Rewrite (@fecomp_r_empty vatom tatom) : term_db.

Hint Resolve fclosed_no_tecapture : term_db.
Hint Resolve fclosed_no_ecapture : term_db.
Hint Resolve no_ecapture_not_egenerated : term_db.

Ltac run_ax :=
  match goal with
  | |- prove (?l1 ++ ?B :: ?l2) ?A => (try now apply ax);
         rewrite <- (app_nil_l l2); rewrite app_comm_cons, app_assoc; run_ax
  end.
Ltac auto_ax := rewrite <- (app_nil_l _); run_ax.


(* Translation of terms and formulas: trivial embedding *)
Notation h2n_term := (@tesubs vatom tatom Empty_set nat r_h2n).
Notation h2n_formula := (@esubs vatom tatom fatom Nocon Icon Qcon Empty_set nat r_h2n).

Lemma h2n : forall A, hprove A ->
  forall L, Forall (fun z => closed z) (map snd L) -> incl (freevars A) (map fst L) ->
  prove nil (h2n_formula A)[[L]].
Proof.
intros A pi; induction pi; intros L Hcl Hsub;
  simpl; rewrite ? multi_subs_fbin;
  remember ((h2n_formula A)[[L]]) as AA;
  (try remember ((h2n_formula B)[[L]]) as BB);
  (try remember ((h2n_formula C)[[L]]) as CC);
  repeat apply impi.
- change (BB :: AA :: nil) with ((BB :: nil) ++ AA :: nil); apply ax.
- apply (impe BB).
  + apply (impe AA).
    * change (AA :: AA → BB :: AA → BB → CC :: nil)
        with ((AA :: AA → BB :: nil) ++ AA → BB → CC :: nil); apply ax.
    * apply ax_hd.
  + apply (impe AA).
    * change (AA :: AA → BB :: AA → BB → CC :: nil)
        with ((AA :: nil) ++ AA → BB :: AA → BB → CC :: nil); apply ax.
    * apply ax_hd.
- remember (map (fun x => (x, evar 0 : term)) (freevars A)) as LA.
  assert (Forall (fun z => closed z) (map snd LA)) as HcLA
    by (subst LA; remember (freevars A) as l; clear; induction l; simpl; intuition).
  assert (map fst LA = freevars A) as HfstLA
    by (subst LA; remember (freevars A) as l; clear;
          induction l; simpl; try rewrite IHl; intuition).
  remember ((h2n_formula A)[[L ++ LA]]) as AAA.
  apply (impe AAA).
  + specialize IHpi1 with (L ++ LA).
    simpl in IHpi1; rewrite ? multi_subs_fbin in IHpi1.
    subst AAA BB; rewrite multi_subs_extend with (L':= LA) (A0:= h2n_formula B);
      [ apply IHpi1 | assumption | rewrite freevars_esubs_fclosed ]; rewrite ? map_app; intuition.
    * apply Forall_app; intuition.
    * apply incl_app; [ apply incl_appr | apply incl_appl ]; intuition.
      rewrite HfstLA; apply incl_refl.
  + subst AAA; apply IHpi2; rewrite ? map_app.
    * apply Forall_app; intuition.
    * apply incl_appr; rewrite HfstLA; apply incl_refl.
- rewrite multi_subs_fqtf, subs_esubs_notegen, multi_subs_subs; intuition.
  + destruct (in_dec eq_dt_dec x (freevars (h2n_formula A))) as [Hf|Hf].
    * apply frle; [ | apply ax_hd ].
      clear - f Hcl Hsub Hf.
      apply multi_tsubs_closed; [ assumption | ].
      intros z Hinz.
      apply Hsub; simpl.
      rewrite freevars_esubs_fclosed in Hf; [ | intuition ].
      rewrite tvars_tesubs_fclosed in Hinz; [ | intuition ].
      apply no_capture_subs_freevars with (x0:= z) (u:= t) in Hf; intuition.
      now specialize_Forall f with z.
    * assert (x ∉ (h2n_formula A)[[L ∖ x]]) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_freevars in Hin; try assumption.
        apply incl_Forall with (map snd L); intuition.
        clear; induction L; intuition; simpl; case_analysis; intuition. }
      rewrite nfree_subs by assumption.
      rewrite <- (nfree_subs _ (evar 0) _ Hnin).
      apply frle; [ reflexivity | ].
      rewrite nfree_subs by assumption.
      apply ax_hd.
  + apply Forall_forall; intros z Hinz.
    rewrite tvars_tesubs_fclosed in Hinz; [ | intuition ].
    specialize_Forall f with z.
    apply no_capture_esubs; intuition.
- rewrite ? multi_subs_fqtf.
  rewrite <- @multi_subs_remove with (x:=x) in HeqAA; try assumption.
  + apply frli; simpl.
    apply impe with (AA↑); [ | apply ax_hd ].
    rewrite multi_subs_fbin; simpl; rewrite <- HeqAA.
    replace (AA↑ → (h2n_formula B)[[L ∖ x]]↑[evar 0//x])
       with ((AA↑ → (h2n_formula B)[[L ∖ x]]↑)[evar 0//x]).
    { apply frle; intuition; auto_ax. }
    simpl; f_equal; apply nfree_subs.
    intros Hin; apply n.
    rewrite freevars_fup in Hin; subst.
    apply multi_subs_freevars in Hin.
    * now rewrite <- freevars_esubs_fclosed with (r:= r_h2n).
    * apply incl_Forall with (map snd L); intuition.
      clear; induction L; intuition; simpl; case_analysis; intuition.
  + now rewrite freevars_esubs_fclosed.
- rewrite multi_subs_fqtf.
  apply frli; simpl.
  rewrite multi_subs_esubs, esubs_comp, esubs_ext with (r2:=r_h2n); intuition.
  replace (((h2n_formula A)[[map (fun '(x0, u) => (x0, tesubs ⇑ u)) (L ∖ x)]])[evar 0//x])
     with (((h2n_formula A)[[map (fun '(x0, u) => (x0, tesubs ⇑ u)) (L ∖ x)
                             ++ (x, evar 0) :: nil]]))
    by now unfold multi_subs; rewrite fold_left_app; simpl.
  apply IHpi.
  + rewrite map_app; apply Forall_app; split.
    * rewrite map_map; simpl; rewrite <- map_map.
      revert Hcl; clear; induction L; simpl; intros HF; [ now constructor | destruct a ].
      simpl in HF; inversion_clear HF.
      case_analysis; intuition; constructor; rcauto.
      now rewrite tvars_fup.
    * now repeat constructor.
  + clear - Hsub; simpl in Hsub.
    intros z Hinz.
    revert Hsub; case (eq_dt_reflect z x); intros Heq Hsub; subst;
      rewrite map_app; simpl; try in_solve.
    rewrite map_map, map_ext with (g:= fst) by (intros [? ?]; reflexivity).
    rewrite <- remove_assoc_remove.
    eapply in_in_remove with (y:= x) in Hinz; intuition ; apply Hsub in Hinz.
    apply in_in_remove with (eq_dec:= eq_dt_dec) (y:= x) in Hinz; intuition.
- rewrite multi_subs_fqtf, subs_esubs_notegen; intuition.
  rewrite multi_subs_subs; try assumption.
  + destruct (in_dec eq_dt_dec x (freevars (h2n_formula A))) as [Hf|Hf].
    * eapply exsi; [ | apply ax_hd ].
      clear - f Hcl Hsub Hf.
      apply multi_tsubs_closed; [ assumption | ].
      intros z Hinz.
      apply Hsub; simpl.
      rewrite freevars_esubs_fclosed in Hf; intuition.
      rewrite tvars_tesubs_fclosed in Hinz; intuition.
      apply no_capture_subs_freevars with (x0:= z) (u:= t) in Hf; intuition.
      now specialize_Forall f with z.
    * assert (x ∉ (h2n_formula A)[[L ∖ x]]) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_freevars in Hin; try assumption.
        apply incl_Forall with (map snd L); intuition.
        clear; induction L; intuition; simpl; case_analysis; intuition. }
      rewrite nfree_subs by assumption.
      apply exsi with (evar 0); [ reflexivity | ].
      rewrite nfree_subs by assumption.
      apply ax_hd.
  + apply Forall_forall; intros z Hinz.
    rewrite tvars_tesubs_fclosed in Hinz; [ | intuition ].
    specialize_Forall f with z.
    now apply no_capture_esubs.
- rewrite 2 multi_subs_fqtf.
  rewrite <- @multi_subs_remove with (x:=x) in HeqBB; try assumption.
  + apply @exse with (x:=x) (A:= (h2n_formula A)[[L ∖ x]]); [ apply ax_hd | ].
    apply impe with ((h2n_formula A)[[L ∖ x]]↑[evar 0//x]); [ | apply ax_hd ].
    replace ((h2n_formula A)[[L ∖ x]]↑[evar 0//x] → BB↑)
       with (((h2n_formula A)[[L ∖ x]]↑ → BB↑)[evar 0//x]).
    { apply frle; [ reflexivity | simpl; rewrite multi_subs_fbin; subst; auto_ax ]. }
    simpl; f_equal; apply nfree_subs.
    intros Hin; apply n.
    rewrite freevars_fup in Hin; subst.
    apply multi_subs_freevars in Hin.
    * now rewrite <- freevars_esubs_fclosed with (r:=r_h2n).
    * apply incl_Forall with (map snd L); intuition.
      clear; induction L; intuition; simpl; case_analysis; intuition.
  + now rewrite freevars_esubs_fclosed.
Qed.

End H2N.
