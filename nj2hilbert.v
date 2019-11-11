(* From Natural Deduction to Hilbert *)

Require Import stdlib_more.
Require Import nj1 hilbert.


Section N2H.

Context { vatom : InfDecType } { tatom : Type } { fatom : Type }.
Notation vfresh := (@fresh vatom).
Notation vfresh_prop := (@fresh_prop vatom).
Notation term := (@term vatom tatom).
Notation closed t := (freevars t = nil).
Notation tup := (@tup vatom tatom).
Notation hterm := (@hterm vatom tatom).
Notation hclosed t := (hfreevars t = nil).
Notation formula := (@formula vatom tatom fatom).
Notation hformula := (@hformula vatom tatom fatom).
Infix "⟶" := himp (at level 70, right associativity).

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

Ltac term_induction t :=
  (try intros until t) ;
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  apply (term_ind_list_Forall t) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ;
    repeat (rewrite flat_map_concat_map) ; repeat (rewrite map_map) ;
    try f_equal ;
    try (apply map_ext_in ; intros i Hi; specialize_Forall_all i) ;
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i) ;
    try assumption ] ;
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


Section Fixed_r.

Variable r : nat -> hterm.

(* Capture-avoiding property *)

Fixpoint ltgood_for lv (t : term) :=
match t with
| dvar n => Forall (fun x => ~ In x (hfreevars (r n))) lv
| tvar x => True
| tconstr f l => fold_right (fun x P => and (ltgood_for lv x) P) True l
end.

Lemma ltgood_for_less : forall x lv1 lv2 t, ltgood_for (lv1 ++ x :: lv2) t -> ltgood_for (lv1 ++ lv2) t.
Proof. term_induction t; intros HF.
- apply Forall_app_inv in HF; destruct HF as [HF1 HF2].
  apply Forall_app; now inversion HF2.
- apply Forall_fold_right in IHl.
  revert IHl HF; clear; induction l; simpl; intros Hl HF.
  + constructor.
  + destruct Hl as [Hl1 Hl2]; destruct HF as [HF1 HF2]; auto.
Qed.

Lemma ltgood_for_closed : forall l t, (forall n, hclosed (r n)) -> ltgood_for l t.
Proof.
intros l t Hc.
term_induction t.
- rewrite (Hc n).
  apply Forall_forall; auto.
- now apply Forall_fold_right.
Qed.

Fixpoint lgood_for lv (A : formula) :=
match A with
| var X l => fold_right (fun x P => and (ltgood_for lv x) P) True l
| imp B C => lgood_for lv B /\ lgood_for lv C
| frl z B => lgood_for (z :: lv) B
| exs z B => lgood_for (z :: lv) B
end.

Lemma lgood_for_less : forall x lv1 lv2 A, lgood_for (lv1 ++ x :: lv2) A -> lgood_for (lv1 ++ lv2) A.
Proof. intros x lv1 lv2 A; revert lv1 lv2; formula_induction A.
- revert H; induction l; simpl; intros Hl.
  + constructor.
  + destruct Hl as [Hl1 Hl2]; split; auto.
    now apply ltgood_for_less with x.
- now rewrite app_comm_cons in H; apply IHA in H.
- now rewrite app_comm_cons in H; apply IHA in H.
Qed.

Lemma lgood_for_closed : forall l A, (forall n, hclosed (r n)) -> lgood_for l A.
Proof.
intros l A Hc; revert l.
formula_induction A.
apply Forall_fold_right.
apply Forall_forall; intros.
now apply ltgood_for_closed.
Qed.

Fixpoint n2h_term t :=
match t with
| dvar n => r n
| tvar x => hvar x
| tconstr f l => hconstr f (map n2h_term l)
end.

Lemma n2h_hfreevars : forall t, incl (freevars t) (hfreevars (n2h_term t)).
Proof. term_induction t; intros z Hin.
- inversion Hin.
- revert IHl Hin; induction l; simpl; intros Hl Hin; auto.
  inversion Hl; subst.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; auto.
Qed.

Fixpoint n2h_formula (A : formula) :=
match A with
| var X l => hfvar X (map n2h_term l)
| imp B C => himp (n2h_formula B) (n2h_formula C)
| frl y B => hfrl y (n2h_formula B)
| exs y B => hexs y (n2h_formula B)
end.

Lemma n2h_tsubs : forall x u t lv, In x lv -> ltgood_for lv t ->
  n2h_term (tsubs x u t) = htsubs x (n2h_term u) (n2h_term t).
Proof. term_induction t; intros lv Hin Hg.
- apply Forall_forall with (x:=x) in Hg; [ | assumption ].
  symmetry; now apply nfree_htsubs.
- f_equal.
  apply map_ext_in; intros a Hina.
  apply Forall_forall with (x:=a) in IHl; [ | assumption ].
  apply (IHl _ Hin).
  apply Forall_fold_right in Hg.
  now apply Forall_forall with (x:=a) in Hg.
Qed.

Lemma n2h_subs : forall x u A lv, In x lv -> lgood_for lv A ->
  n2h_formula (subs x u A) = hfsubs x (n2h_term u) (n2h_formula A).
Proof. formula_induction A.
- now simpl in H0; apply n2h_tsubs with lv.
- now simpl in H0.
- now apply A1 with lv.
- now apply IHA1 with lv.
- case_analysis; [ reflexivity | ].
  rewrite <- (app_nil_l _) in H0; apply lgood_for_less in H0.
  now f_equal; apply IHA with lv.
- case_analysis; [ reflexivity | ].
  rewrite <- (app_nil_l _) in H0; apply lgood_for_less in H0.
  now f_equal; apply IHA with lv.
Qed.

Lemma lgood_hgood_closed : forall u x lv lv' A,
  closed u -> lgood_for lv (subs x u A) -> In x lv' -> lgood_for lv' A ->
  Forall (fun y => hgood_for x y (n2h_formula A)) (hfreevars (n2h_term u)).
Proof.
intros u x lv lv' A; revert lv; formula_induction A.
- now apply Forall_forall.
- apply Forall_and.
  + now apply A1 with lv.
  + now apply IHA1 with lv.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  revert H0; case_analysis; intros H0.
  + subst.
    apply Forall_forall; intros z Hz Hin.
    exfalso.
    now apply in_remove in Hin.
  + assert (Hg := H0).
    apply IHA in H0; auto.
    2:{ now rewrite <- (app_nil_l _) in H2; apply lgood_for_less in H2. }
    apply Forall_forall; intros z Hz Hin.
    apply Forall_forall with (x:=z) in H0; [ | assumption ].
    split; [ assumption | ].
    intros Heq2; subst.
    apply in_remove in Hin; destruct Hin as [Hin _].
    simpl in Hg.
    clear - H Hg Hz Hin H1 H2.
    remember (x0 :: lv) as lv0.
    assert (In x0 lv0) by (now subst; constructor); clear lv Heqlv0.
    rewrite <- (app_nil_l _) in H2; apply lgood_for_less in H2; simpl in H2.
    { revert lv0 lv' Hg H0 Hin H1 H2; formula_induction A.
      - apply Forall_fold_right in Hg.
        apply Forall_fold_right in H2.
        revert Hg Hin H2; induction l; simpl; intros Hg Hin H2; [ assumption | ].
        inversion Hg; inversion H2; subst.
        apply in_app_or in Hin; destruct Hin as [Hin|Hin].
        + revert Hin H5 H9; clear - H Hz H0 H1; term_induction a; simpl; intros Hinlv Hg Hlv' .
          * apply Forall_forall with (x:=x) in Hlv'; auto.
          * destruct Hinlv; subst; [ | assumption ].
            rewrite eqb_refl in Hg.
            revert H Hz Hg; clear - H0; term_induction u; simpl; intros Hc Hin Hg.
            -- now apply Forall_forall with (x:=x0) in Hg.
            -- inversion Hc.
            -- apply Forall_fold_right in Hg.
               revert IHl Hc Hin Hg; induction l; simpl; intros Hl Hc Hin Hg; [ assumption | ].
               apply app_eq_nil in Hc.
               inversion Hl; inversion Hg; inversion Hc; subst.
               apply in_app_or in Hin; destruct Hin as [Hin|Hin].
               ++ now apply H2.
               ++ now apply IHl in H3.
          * apply Forall_fold_right in Hg.
            apply Forall_fold_right in Hlv'.
            revert IHl Hinlv Hg Hlv'; induction l; intros; simpl in Hinlv.
            -- inversion Hinlv.
            -- apply in_app_or in Hinlv; destruct Hinlv as [Hinlv|Hinlv].
               ++ inversion IHl0; inversion Hg; inversion Hlv'; subst.
                  apply H4; auto.
               ++ inversion IHl0; inversion Hg; inversion Hlv'; subst.
                  apply IHl; auto.
        + now apply IHl.
      - apply in_app_or in Hin; destruct Hin.
        + now apply A1 with lv0 lv'.
        + now apply IHA1 with lv0 lv'.
      - revert Hg; case_analysis; intros Hg.
        { apply in_remove in Hin.
          now apply Hin. }
        apply IHA with (x1 :: lv0) (x1 :: lv'); auto.
        + now apply in_cons.
        + now apply in_remove in Hin.
        + now apply in_cons.
      - revert Hg; case_analysis; intros Hg.
        { apply in_remove in Hin.
          now apply Hin. }
        apply IHA with (x1 :: lv0) (x1 :: lv'); auto.
        + now apply in_cons.
        + now apply in_remove in Hin.
        + now apply in_cons. }
Qed.



Fixpoint s2f l (A : formula) :=
match l with
| nil => A
| B :: tl => s2f tl (imp B A)
end.

Notation n2h_sequent l A := (n2h_formula (s2f l A)).

Lemma hprove_Bsequent :
  forall l A B, hprove ((n2h_formula A ⟶ n2h_formula B) ⟶ n2h_sequent l A ⟶ n2h_sequent l B).
Proof.
induction l; intros A B; simpl.
- apply hprove_I.
- specialize IHl with (imp a A) (imp a B); simpl in IHl.
  eapply hprove_CUT; [ | apply IHl ].
  apply hprove_B.
Qed.

Lemma hprove_Ssequent : forall l A B, hprove (n2h_sequent l (imp A B) ⟶ n2h_sequent l A ⟶ n2h_sequent l B).
Proof.
induction l; intros A B; simpl.
- apply hprove_I.
- specialize IHl with (imp a A) (imp a B); simpl in IHl.
  eapply hprove_CUT; [ | apply IHl ].
  eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_S ].
Qed.

Lemma hprove_sequent_imp : forall l A B,
  hprove (n2h_sequent l (imp A B)) -> hprove (n2h_formula A ⟶ n2h_sequent l B).
Proof.
induction l; simpl; intros A B pi; auto.
apply IHl.
eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply pi ]; simpl.
apply hprove_C.
Qed.

Lemma hprove_imp_sequent : forall l A B,
  hprove (n2h_formula A ⟶ n2h_sequent l B) -> hprove (n2h_sequent l (imp A B)).
Proof.
induction l; simpl; intros A B pi; auto.
apply IHl in pi.
eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply pi ]; simpl.
apply hprove_C.
Qed.

Lemma hprove_FRLsequent : forall x l A, ~ In x (flat_map (fun C => hffreevars (n2h_formula C)) l) ->
  hprove ((hfrl x (n2h_sequent l A)) ⟶ n2h_sequent l (frl x A)).
Proof.
induction l; simpl; intros A Hf.
- apply hprove_I.
- eapply hprove_CUT; [ apply IHl | ].
  + intros Hin; apply Hf.
    now apply in_or_app; right.
  + eapply hprove_MP; [ apply hprove_Bsequent | ].
    simpl; apply hprove_FRL.
    intros Hin; apply Hf.
    now apply in_or_app; left.
Qed.

End Fixed_r.



(*
Proposition prove_with_prop_has_prop : forall (P : formula -> Prop),
 (forall A, P (fupz A) -> P A) ->
   (forall l A (pi : nprove l A), nprove_with_prop P pi -> Forall P (A :: l))
 * (forall l A (pi : rprove l A), rprove_with_prop P pi -> Forall P (A :: l)).
Proof.
intros P Hfup.
apply rnprove_mutrect ; intros.
- inversion H.
  destruct H1.
  constructor; auto.
  apply Forall_app; auto.
- inversion H1.
  destruct H3.
  apply H in H3.
  inversion H3; subst.
  auto.
- inversion H0.
  apply H in H2.
  inversion H2.
  auto.
- now apply H in H0.
- inversion H0.
  apply H in H2.
  inversion H2; inversion H6; auto.
- inversion H0.
  apply H in H2.
  inversion H2.
  constructor; auto.
  clear - Hfup H6.
  revert H6; induction l; simpl; intros Hf; constructor; inversion Hf; subst; auto.
- inversion H0.
  apply H in H2.
  inversion H2; auto.
- inversion H1.
  destruct H3.
  apply H in H3.
  inversion H3; auto.
Qed.
*)

(*
Theorem subformula_prop_hered : forall (P : formula -> Prop), (forall A B, subform A B -> P B -> P A) ->
   (forall l A (pi : nprove l A), Forall P (A :: l) -> nprove_with_prop P pi)
 * (forall l A (pi : rprove l A), Forall P (A :: l) -> rprove_with_prop P pi).
Proof.
intros P HP; split; intros l A pi HF.
- assert (Hn := fst subformula_prop _ _ pi).
  destruct Hn as [_ Hn].
  apply rnprove_stronger with (Q := P) in Hn; [ assumption | ].
  intros x Hs.
  remember (A :: l) as s.
  revert Hs HF; clear - HP; induction s; intros Hs HF; inversion Hs; inversion HF; subst; auto.
  apply HP with a; auto.
- assert (Hr := snd subformula_prop _ _ pi).
  apply rnprove_stronger with (Q := P) in Hr; [ assumption | ].
  intros x Hs.
  remember (A :: l) as s.
  revert Hs HF; clear - HP; induction s; intros Hs HF; inversion Hs; inversion HF; subst; auto.
  apply HP with a; auto.
Qed.
*)



(*
Inductive lsubform : formula -> formula -> Prop :=
| lsub_id : forall A, lsubform A A
| lsub_imp_r : forall A B C, lsubform (imp A B) C -> lsubform B C
| lsub_frl : forall A x u B, lsubform (frl x A) B -> lsubform (subs x u A) B
| lsub_ex : forall A x u B, lsubform (exs x A) B -> lsubform (subs x u A) B.

Lemma lsubform_trans : forall A B C, lsubform A B -> lsubform B C -> lsubform A C.
Proof.
intros A B C Hl Hr ; revert C Hr ; induction Hl ; intros C' Hr; auto;
  try (econstructor; now apply IHHl).
Qed.

Lemma subform_fupz : forall A B, subform A B -> subform (fupz A) (fupz B).
Proof.
intros A B Hs; induction Hs; try (now econstructor; eauto).
- rewrite fup_subs_com in IHHs.
  now econstructor; eauto.
- rewrite fup_subs_com in IHHs.
  now econstructor; eauto.
- eapply subform_trans; [ apply IHHs | ].
  simpl; rewrite fup_subs_com.
  econstructor.
  econstructor.
  rewrite fup_subs_com.
  apply sub_id.
- eapply subform_trans; [ apply IHHs | ].
  simpl; rewrite fup_subs_com.
  econstructor.
  econstructor.
  rewrite fup_subs_com.
  apply sub_id.
Qed.

Lemma lsubform_subform : forall A B, lsubform A B -> subform A B.
Proof.
intros A B Hs; induction Hs.
- apply sub_id.
- apply subform_trans with (imp A B); auto.
  now constructor; constructor.
- apply subform_trans with (frl x A); auto.
  now econstructor; constructor.
- apply subform_trans with (exs x A); auto.
  now econstructor; constructor.
Qed.

Theorem lsubformula_prop :
   (forall l A (pi : nprove l A), Exists (lsubform A) l
                               /\ nprove_with_prop (fun B => Exists (subform B) (A :: l)) pi)
 * (forall l A (pi : rprove l A), rprove_with_prop (fun B => Exists (subform B) (A :: l)) pi).
Proof.
apply rnprove_mutrect; simpl.
- intros l1 l2 B ; repeat split.
  + apply Exists_exists ; exists B ; split ; [ | constructor ].
    apply in_app_iff ; right ; constructor ; reflexivity.
  + rewrite <- (app_nil_l l1) ; rewrite <- app_assoc ; rewrite app_comm_cons.
    remember (B :: nil) as l0 ; clear Heql0 ; revert l0.
    induction l1 ; intros l0 ; constructor.
    * apply Exists_exists ; exists a ; split ; [ | constructor ].
       apply in_app_iff ; right ; constructor ; reflexivity.
    * rewrite <- app_comm_cons ; rewrite <- (app_nil_l l1) ; rewrite <- app_assoc ;
        rewrite app_comm_cons ; rewrite app_assoc.
      apply IHl1.
  + rewrite <- (app_nil_l l2) ; rewrite 2 app_comm_cons ; rewrite app_assoc.
    remember ((B :: l1) ++ B :: nil) as l0 ; clear Heql0 ; revert l0 ; simpl.
    induction l2 ; intros l0 ; constructor.
    * apply Exists_exists ; exists a ; split ; [ | constructor ].
       apply in_app_iff ; right ; constructor ; reflexivity.
    * rewrite <- (app_nil_l l2) ; rewrite app_comm_cons ; rewrite app_assoc.
      apply IHl2.
  + constructor ; constructor.
- intros l' B' A' pi1 [Hn Hs1] pi2 Hs2 ; repeat split.
  + eapply Exists_impl ; [ | eassumption ].
    intros C HsC.
    apply lsubform_trans with (imp A' B'); auto.
    econstructor; constructor.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      apply lsubform_subform in HsD.
      eapply subform_trans; eassumption.
    * constructor ; assumption.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      eapply subform_trans ; [ eassumption | ].
      apply lsubform_subform in HsD.
      apply subform_trans  with (imp A' B'); [ constructor ; constructor | eassumption ].
    * constructor ; assumption.
- intros x l' A' u Hc pi [Hn Hs] ; repeat split.
  + eapply Exists_impl ; [ | eassumption ].
    intros C HsC.
    eapply lsubform_trans ; [ econstructor ; constructor | eassumption ].
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      apply lsubform_subform in HsD.
      eapply subform_trans; eassumption.
    * constructor ; assumption.
- intros.
  apply H.
- intros l' A' B' pi Hs ; split.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | apply Hs ] ; simpl.
    intros C P.
    inversion P ; subst.
    * constructor ; now constructor.
    * inversion H0 ; subst.
      -- constructor ; now constructor.
      -- constructor ; assumption.
- intros x l' A' pi Hs ; split.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | apply Hs ] ; simpl.
    intros C P.
    inversion P ; subst.
    * constructor.
      eapply subform_trans ; [ eassumption | constructor ; constructor ].
    * apply Exists_cons_tl.
      revert H0 ; clear ; induction l' ; intros H ; inversion H ; subst.
      -- constructor.
         eapply subform_trans ; [ eassumption | constructor ; constructor ].
      -- apply Exists_cons_tl ; intuition.
- intros x l' A' u Hc pi Hs ; split.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | apply Hs ] ; simpl.
    intros C P.
    inversion P ; subst.
    * constructor.
      eapply subform_trans ; [ eassumption | econstructor ; constructor ].
    * constructor ; assumption.
- intros l' C x A' pi1 [Hn Hs1] pi2 Hs2 ; repeat split.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros D HsD.
    inversion HsD ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros E HsE.
      apply lsubform_subform in HsE.
      eapply subform_trans; eassumption.
    * constructor ; assumption.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros D HsD.
    inversion HsD ; subst.
    * constructor.
      eapply subform_trans ; [ eassumption | constructor ; constructor ].
    * inversion H0 ; subst ; apply Exists_cons_tl.
      -- eapply Exists_impl ; [ | eassumption ].
         intros E HsE.
         eapply subform_trans ; [ eassumption | ].
         apply lsubform_subform in HsE.
         eapply subform_trans with (exs x A'); [ constructor ; constructor | eassumption ].
      -- revert H1 ; clear ; induction l' ; intros H ; inversion H ; subst.
         ++ constructor.
            eapply subform_trans ; [ eassumption | constructor ; constructor ].
         ++ apply Exists_cons_tl ; intuition.
Qed.
*)
















Notation n2h_sequent r l A := (n2h_formula r (s2f l A)).
Notation rgood_for r := (lgood_for r nil).

Lemma n2h_allvars : forall r A,
  incl (allvars A ++ hffreevars (n2h_formula r A)) (hallvars (n2h_formula r A)).
Proof. formula_induction A; simpl; intros z Hin.
- revert Hin; induction l; simpl; intros Hin.
  + assumption.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
    apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; auto.
    * now apply n2h_hfreevars.
    * apply IHl.
      apply in_or_app; auto.
- apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right].
    * apply A1.
      now apply in_or_app; left.
    * apply IHA1.
      now apply in_or_app; left.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right].
    * apply A1.
      now apply in_or_app; right.
    * apply IHA1.
      now apply in_or_app; right.
- inversion Hin; subst.
  + now constructor.
  + apply in_cons, IHA.
    apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right]; auto.
    now apply in_remove in H.
- inversion Hin; subst.
  + now constructor.
  + apply in_cons, IHA.
    apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right]; auto.
    now apply in_remove in H.
Qed.

Definition rsubs x y (r : nat -> hterm) n := htsubs x (hvar y) (r n).

Lemma tgood_for_fresh : forall r y x t, ~ In y (freevars t) -> forall lv, ~ In y lv ->
  ltgood_for r lv t -> ltgood_for (rsubs x y r) lv t.
Proof.
term_induction t; intros Hin lv Hin2 Hg.
- revert Hin2 Hg; clear; induction lv; simpl; intros Hin Hg; constructor; inversion Hg; subst; auto.
  intros Hin2; apply H1.
  unfold rsubs in Hin2.
  apply hfreevars_tsubs in Hin2; destruct Hin2 as [Hin2|Hin2]; simpl in Hin2.
  + exfalso; destruct Hin2; destruct H; auto.
  + now destruct Hin2.
- apply Forall_fold_right; apply Forall_fold_right in Hg.
  revert IHl Hin Hg; induction l; simpl; intros Hl Hin Hg; constructor; inversion Hg; inversion Hl; subst; auto.
  + apply H5; auto.
    intros Hin3; apply Hin.
    apply in_or_app; auto.
  + apply IHl; auto.
    intros Hin3; apply Hin.
    apply in_or_app; auto.
Qed.

Lemma good_for_fresh : forall r y x A, ~ In y (allvars A) -> forall lv, ~ In y lv ->
  lgood_for r lv A -> lgood_for (rsubs x y r) lv A.
Proof. formula_induction A.
- apply Forall_fold_right in H1; apply Forall_fold_right.
  revert H H1; induction l; simpl; intros Hin HF; constructor; inversion HF; subst.
  + apply tgood_for_fresh; auto.
    intros Hin2; apply Hin.
    apply in_or_app; auto.
  + apply IHl; auto.
    intros Hin2; apply Hin.
    apply in_or_app; auto.
- apply IHA; intuition.
  apply H0; inversion H2; intuition.
- apply IHA; intuition.
  apply H0; inversion H2; intuition.
Qed.




(* Freshness function now required *)

Fixpoint rrefresh l ld r :=
match l with
| nil => r
| x :: tl => let y := vfresh (l ++ ld) in rrefresh tl (x :: y :: ld) (rsubs x y r)
end.

Lemma hfreevars_rrefresh : forall n l ld r z,
  In z ld -> In z (hfreevars (rrefresh l ld r n)) -> In z (hfreevars (r n)).
Proof.
induction l; intros ld r z Hinz Hin; simpl in Hin; auto.
apply IHl in Hin.
- unfold rsubs in Hin.
  apply hfreevars_tsubs in Hin.
  destruct Hin as [Hin|Hin].
  + exfalso.
    simpl in Hin; destruct Hin as [Hin _].
    destruct Hin; auto.
    apply vfresh_prop with (a :: l ++ ld).
    rewrite H.
    apply in_cons.
    now apply in_or_app; right.
  + now destruct Hin.
- now apply in_cons, in_cons.
Qed.

Lemma rrefresh_notin : forall n z lvA lv r,
  In z lvA -> In z (hfreevars (rrefresh lvA lv r n)) -> False.
Proof.
induction lvA; intros lv r Hinz Hin; inversion Hinz; subst; simpl in Hin.
- clear - Hin.
  apply hfreevars_rrefresh in Hin.
  + unfold rsubs in Hin.
    apply hfreevars_tsubs in Hin.
    destruct Hin as [Hin|Hin].
    * destruct Hin as [Hin _].
      simpl in Hin; destruct Hin; auto.
      apply vfresh_prop with (z :: lvA ++ lv).
      rewrite H.
      now constructor.
    * now destruct Hin.
  + now constructor.
- apply IHlvA in Hin; auto.
Qed.

Lemma good_for_refresh_preserv : forall l r ld lv A, incl (allvars A) ld -> incl lv ld ->
  lgood_for r lv A -> lgood_for (rrefresh l ld r) lv A.
Proof.
induction l; intros r ld lv A HA Hlv Hg; simpl; auto.
apply IHl.
- intros z Hz.
  apply in_cons, in_cons.
  apply HA, Hz.
- intros z Hz.
  apply in_cons, in_cons.
  apply Hlv, Hz.
- apply good_for_fresh; auto; intros Hin.
  + apply HA in Hin.
    apply vfresh_prop with (a :: l ++ ld).
    apply in_cons.
    now apply in_or_app; right.
  + apply Hlv in Hin.
    apply vfresh_prop with (a :: l ++ ld).
    apply in_cons.
    now apply in_or_app; right.
Qed.

Lemma good_for_refresh : forall ld A r lvA lv, incl (hallvars (n2h_formula r A) ++ lv) lvA ->
  lgood_for (rrefresh lvA ld r) lv A.
Proof. formula_induction A.
- apply Forall_fold_right.
  revert H; induction l; intros HlvA; constructor.
  + clear IHl; term_induction a; simpl.
    * apply Forall_forall; intros z Hz Hin.
      eapply rrefresh_notin; [ | eassumption ].
      apply HlvA; now apply in_or_app; right.
    * apply Forall_fold_right.
      apply Forall_forall; intros t Ht.
      apply Forall_forall with (x:=t) in IHl; auto.
  + clear - HlvA.
    apply Forall_forall; intros t Ht.
    term_induction t; auto.
    * apply Forall_forall; intros z Hz Hin.
      eapply rrefresh_notin; [ | eassumption ].
      apply HlvA; now apply in_or_app; right.
    * apply Forall_fold_right.
      apply Forall_forall; intros u Hu.
      apply Forall_forall with (x:=u) in IHl; auto.
- apply A1.
  intros z Hz; apply H.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; auto.
  now apply in_or_app; left.
- apply IHA1.
  intros z Hz; apply H.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; auto.
  now apply in_or_app; right.
- apply IHA.
  intros z Hz.
  apply H.
  apply in_app_or in Hz; destruct Hz as [Hz|Hz]; auto.
  + right; now apply in_or_app; left.
  + destruct Hz; [left|right]; auto.
    now apply in_or_app; right.
- apply IHA.
  intros z Hz.
  apply H.
  apply in_app_or in Hz; destruct Hz as [Hz|Hz]; auto.
  + right; now apply in_or_app; left.
  + destruct Hz; [left|right]; auto.
    now apply in_or_app; right.
Qed.

Lemma bisubs_fresh : forall r y x A,
  ~ In y (allvars A) -> ~ In y (hffreevars (n2h_formula r A)) ->
  hfsubs y (hvar x) (n2h_formula (rsubs x y r) A) = n2h_formula r A.
Proof. formula_induction A.
- revert H H0; clear; term_induction t; simpl; intros Hin Hinf.
  + unfold rsubs.
    remember (r n) as u; revert Hinf; clear; hterm_induction u; simpl; intros Hinf.
    f_equal.
    rewrite <- (map_id l) at 2.
    apply map_ext_in; intros a Hina.
    apply Forall_forall with (x:=a) in IHl; auto.
    apply IHl.
    intros Hin; apply Hinf.
    apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [ left | right ]; subst; auto.
    * revert Hina; clear - Hin; induction l; simpl; intros Hin2; auto.
      apply in_or_app; destruct Hin2 as [Hin2|Hin2]; [ left | right ]; subst; auto.
    * now (rewrite flat_map_concat_map, map_map in Hin).
  + f_equal.
    apply map_ext_in; intros a Hina.
    apply Forall_forall with (x:=a) in IHl; [ | assumption ].
    apply IHl; rewrite flat_map_concat_map.
    * simpl; intros Hin2; apply Hin.
      apply in_or_app; apply in_app_or in Hin2; destruct Hin2 as [Hin2|Hin2]; [ left | right ]; auto.
      revert Hina; clear - Hin2; induction l; simpl; intros Hin; auto.
      apply in_or_app; destruct Hin as [Hin|Hin]; [ left | right ]; subst; auto.
    * simpl; intros Hin2.
      apply Hinf.
      apply in_or_app; apply in_app_or in Hin2; destruct Hin2 as [Hin2|Hin2]; [left|right].
      -- revert Hina; clear - Hin2; induction l; simpl; intros Hin; auto.
         apply in_or_app; destruct Hin as [Hin|Hin]; [ left | right ]; subst; auto.
      -- now rewrite map_map in Hin2.
- apply H.
  simpl; apply in_or_app; auto.
- apply H0.
  simpl; apply in_or_app; right; auto.
- case_analysis; f_equal; intuition.
  apply H.
  intros Hin; apply H0.
  apply notin_remove; auto.
- case_analysis; f_equal; intuition.
  apply H.
  intros Hin; apply H0.
  apply notin_remove; auto.
Qed.

Lemma good_for_hilbert_rsubs : forall r y x A,
  ~ In y (allvars A) -> ~ In y (hffreevars (n2h_formula r A)) -> rgood_for r A ->
  hprove (n2h_formula (rsubs x y r) A) -> hprove (n2h_formula r A).
Proof.
intros r y x A Hin Hinf Hg pi.
rewrite <- bisubs_fresh with (x:=x) (y:=y); auto.
eapply hprove_MP; [ apply hprove_INST | apply hprove_GEN ]; auto.
simpl; repeat constructor.
revert Hin Hinf Hg; clear.
induction A; simpl; intros; auto.
- split.
  + apply IHA1.
    * intros Hin2; apply Hin.
      apply in_or_app; auto.
    * intros Hin2; apply Hinf.
      apply in_or_app; auto.
    * destruct Hg; auto.
  + apply IHA2.
    * intros Hin2; apply Hin.
      apply in_or_app; auto.
    * intros Hin2; apply Hinf.
      apply in_or_app; auto.
    * destruct Hg; auto.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  split.
  + apply IHA; auto.
    * rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
      intros Heq; subst.
      apply in_remove in H; destruct H.
      apply Hinf.
      apply notin_remove; auto.
    * rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
  + intros Heq; subst.
    revert Hinf H Hin Hg; clear; formula_induction A.
    * apply Forall_fold_right in Hg.
      apply in_remove in H; destruct H.
      apply Hinf.
      apply notin_remove; auto.
      revert H Hin Hg; clear; induction l; simpl; intros; auto.
      inversion Hg; subst.
      apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right].
      -- revert H H2 Hin; clear; term_induction a; intros.
         ++ unfold rsubs in H.
            inversion H2; subst.
            apply hfreevars_tsubs in H; destruct H; auto.
            ** exfalso; destruct H; auto.
            ** now destruct H.
         ++ apply Forall_fold_right in H2.
            revert IHl H H2 Hin; induction l0; intros Hl Hin Hg Hnin.
            ** inversion Hin.
            ** simpl; apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right];
               inversion Hl; inversion Hg; subst.
               --- apply H1; auto.
                   intros Hnin2; apply Hnin.
                   destruct Hnin2; auto.
                   right; rewrite flat_map_concat_map in H.
                   apply in_or_app; apply in_app_or in H; destruct H; [left|right]; auto.
                   now apply in_or_app; left.
               --- apply IHl0; auto.
                   intros Hnin2; apply Hnin.
                   destruct Hnin2; auto.
                   right.
                   simpl; rewrite <- app_assoc.
                   apply in_or_app; right; auto.
      -- apply IHl; auto.
         intros Hin2; apply Hin.
         destruct Hin2; auto.
         right.
         apply in_or_app; auto.
    * apply in_remove in H; destruct H.
      apply in_app_or in H; destruct H as [H|H].
      -- apply A1; auto; intros.
         ++ apply Hinf.
            apply notin_remove; auto.
            apply in_or_app; left.
            apply in_remove in H5; destruct H5; auto.
         ++ apply notin_remove; auto.
         ++ destruct H5; auto.
            apply H3.
            apply in_or_app; auto.
      -- apply IHA1; auto; intros.
         ++ apply Hinf.
            apply notin_remove; auto.
            apply in_or_app; right.
            apply in_remove in H5; destruct H5; auto.
         ++ apply notin_remove; auto.
         ++ destruct H5; auto.
            apply H3.
            apply in_or_app; auto.
    * apply IHA; intuition.
      -- apply Hinf.
         apply notin_remove; auto.
         apply notin_remove; auto.
         apply in_remove in H0; destruct H0; auto.
      -- apply notin_remove; auto.
         apply in_remove in H; destruct H.
         apply in_remove in H; destruct H; auto.
      -- rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
    * apply IHA; intuition.
      -- apply Hinf.
         apply notin_remove; auto.
         apply notin_remove; auto.
         apply in_remove in H0; destruct H0; auto.
      -- apply notin_remove; auto.
         apply in_remove in H; destruct H.
         apply in_remove in H; destruct H; auto.
      -- rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
Qed.

Lemma good_for_hilbert_rrefresh : forall l r ld A,
  incl (hallvars (n2h_formula r A)) ld -> rgood_for r A ->
  hprove (n2h_formula (rrefresh l ld r) A) -> hprove (n2h_formula r A).
Proof.
induction l; intros r ld A HA Hg pi; simpl; auto.
apply IHl in pi.
- apply good_for_hilbert_rsubs in pi; auto.
  + intros Hin.
    apply vfresh_prop with (a :: l ++ ld).
    apply in_cons.
    apply in_or_app; right.
    apply HA.
    apply n2h_allvars.
    now apply in_or_app; left.
  + intros Hin.
    apply vfresh_prop with (a :: l ++ ld).
    apply in_cons.
    apply in_or_app; right.
    apply HA.
    apply n2h_allvars.
    now apply in_or_app; right.
- intros z Hz.
  unfold rsubs in Hz.
  revert HA Hz; clear; formula_induction A; subst.
  + revert HA Hz; induction l0; simpl; intros HA Hz; auto.
    apply in_app_or in Hz; destruct Hz as [Hz|Hz].
    * right.
      revert HA Hz; clear; term_induction a0; simpl; intros HA Hz.
      -- apply hfreevars_tsubs in Hz; destruct Hz as [Hz|Hz]; destruct Hz.
         ++ left.
            simpl in H; now destruct H.
         ++ right.
            apply HA.
            now apply in_or_app; left.
      -- destruct Hz; subst; try now idtac.
         right.
            apply HA.
          now constructor.
      -- revert IHl HA Hz; induction l1; simpl; intros Hl HA Hz; [inversion Hz |].
         inversion Hl; subst.
         apply in_app_or in Hz; destruct Hz as [Hz | Hz].
         ++ apply H1 in Hz; auto.
            intros y Hy; apply HA.
            rewrite map_map in Hy.
            apply in_or_app; apply in_app_or in Hy; destruct Hy as [Hy|Hy]; [left|right]; auto.
            now apply in_or_app; left.
         ++ apply IHl1 in Hz; auto.
            intros y Hy; apply HA.
            apply in_or_app; apply in_app_or in Hy; destruct Hy as [Hy|Hy]; [left|right]; auto.
            now apply in_or_app; right.
    * apply IHl0 in Hz; auto.
      intros y Hy; apply HA.
      now apply in_or_app; right.
  + apply in_app_or in Hz; destruct Hz as [Hz|Hz].
    * apply A1; auto.
      intros y Hy; apply HA.
      now apply in_or_app; left.
    * apply IHA1; auto.
      intros y Hy; apply HA.
      now apply in_or_app; right.
  + destruct Hz as [Hz|Hz].
    * right; right.
      apply HA; now constructor.
    * apply IHA; auto.
      intros y Hy; apply HA; now constructor.
  + destruct Hz as [Hz|Hz].
    * right; right.
      apply HA; now constructor.
    * apply IHA; auto.
      intros y Hy; apply HA; now constructor.
- apply good_for_fresh; auto.
  intros Hin.
  apply vfresh_prop with (a :: l ++ ld).
  apply in_cons.
  apply in_or_app; right.
  apply HA.
  apply n2h_allvars.
  now apply in_or_app; left.
Qed.


Definition rup t r n : hterm :=
match n with
| 0 => t
| S k => r k
end.

Lemma good_for_rup_term : forall t r u lv, ltgood_for r lv u -> ltgood_for (rup t r) lv (tup 0 u).
Proof.
term_induction u; intros lv HF.
apply Forall_fold_right in HF; apply Forall_fold_right.
apply Forall_forall; intros x Hx.
apply in_map_iff in Hx.
destruct Hx as [y [Heq Hy]]; subst.
apply Forall_forall with (x:=y) in HF; [ apply Forall_forall with (x:=y) in IHl | ]; auto.
Qed.

Lemma good_for_rup : forall t r A lv, lgood_for r lv A -> lgood_for (rup t r) lv (fup 0 A).
Proof.
formula_induction A.
apply Forall_fold_right in H; apply Forall_fold_right.
revert H; induction l; simpl; intros HF; inversion HF; subst; constructor.
- now apply good_for_rup_term.
- now apply IHl.
Qed.

Lemma good_for_rup_tsubs : forall r x y lv t,
  ~ In y lv -> ~ In y (hfreevars (n2h_term r t)) ->
  ltgood_for r lv t ->  ltgood_for (rup (hvar y) r) lv (tsubs x (dvar 0) (tup 0 t)).
Proof.
term_induction t; intros Hlv Hy Hg.
- case_analysis; auto.
  apply Forall_forall; intros z Hz; intros Heqz.
  apply Hy; destruct Heqz; subst.
  + now exfalso.
  + inversion H.
- apply Forall_fold_right; apply Forall_fold_right in Hg.
  apply Forall_forall; intros z Hz.
  apply in_map_iff in Hz; destruct Hz as [z' [Heq Hz]]; subst.
  apply Forall_forall with (x:=z') in Hg; apply Forall_forall with (x:=z') in IHl; auto.
  apply IHl; auto.
  intros Hin; apply Hy.
  revert Hz Hin; clear; induction l; simpl; intros Hz Hin; inversion Hz; subst.
  + now apply in_or_app; left.
  + apply in_or_app; right.
    now apply IHl.
Qed.

Lemma good_for_rup_subs : forall r x y A lv,
  In x lv -> ~ In y lv -> ~ In y (hallvars (n2h_formula r A)) ->
  lgood_for r lv A ->  lgood_for (rup (hvar y) r) lv (subs x (dvar 0) (fup 0 A)).
Proof. formula_induction A;
try rename H into Hxlv; try rename H0 into Hylv; try rename H1 into Hyl; try rename H2 into Hg.
- apply Forall_fold_right in Hg; apply Forall_fold_right.
  apply Forall_forall; intros t Ht.
  rewrite map_map in Ht.
  apply in_map_iff in Ht; destruct Ht as [u [Heq Hu]]; subst.
  apply Forall_forall with (x:=u) in Hg; [ | assumption ].
  apply good_for_rup_tsubs; auto.
  intros Hin; apply Hyl.
  revert Hu Hin; clear; induction l; simpl; intros Hu Hin; inversion Hu; subst.
  + now apply in_or_app; left.
  + apply in_or_app; right.
    now apply IHl.
- case_analysis.
  + now apply good_for_rup.
  + apply IHA; auto.
    * now apply in_cons.
    * intros Hin; apply Hylv.
      destruct Hin as [Hin|Hin]; subst; auto.
      exfalso; apply Hyl; now left.
- case_analysis.
  + now apply good_for_rup.
  + apply IHA; auto.
    * now apply in_cons.
    * intros Hin; apply Hylv.
      destruct Hin as [Hin|Hin]; subst; auto.
      exfalso; apply Hyl; now left.
Qed.

Lemma n2h_rup_term : forall t u r, n2h_term (rup t r) (tup 0 u) = n2h_term r u.
Proof.
term_induction u; intros r; f_equal.
rewrite map_map.
apply map_ext_in.
intros a Ha.
apply Forall_forall with (x:=a) in IHl; auto.
Qed.

Lemma n2h_rup : forall t A r, n2h_formula (rup t r) (fup 0 A) = n2h_formula r A.
Proof. formula_induction A; apply n2h_rup_term. Qed.

Lemma n2h_rup_subs : forall x lv t A r, In x lv -> lgood_for r lv A ->
  n2h_formula (rup t r) (subs x (dvar 0) (fup 0 A)) = hfsubs x t (n2h_formula r A).
Proof.
intros.
rewrite n2h_subs with (lv:=lv); auto.
- f_equal.
  apply n2h_rup.
- now apply good_for_rup.
Qed.

Proposition n2h :
   (forall l A, nprove l A -> forall r, Forall (rgood_for r) (A :: l) -> hprove (n2h_sequent r l A))
 * (forall l A, rprove l A -> forall r, Forall (rgood_for r) (A :: l) -> hprove (n2h_sequent r l A)).
Proof.
apply rnprove_mutrect ; intros.
- induction l1; simpl.
  + induction l2; simpl.
    * apply hprove_I.
    * eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_K ] | apply IHl2 ].
      simpl in H; inversion H; inversion H3; inversion H7; subst.
      now simpl; repeat constructor.
  + eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_K ] | apply IHl1 ].
    inversion H; inversion H3; subst.
    now constructor.
- assert ({rf : _ & Forall (rgood_for rf) (imp A B :: l)
                  & hprove (n2h_sequent rf l B) -> hprove (n2h_sequent r0 l B)})
    as [rf Hg Hp].
  { exists (rrefresh (hallvars (n2h_formula r0 A))
                     (flat_map (fun C => hallvars (n2h_formula r0 C)) (B :: l)) r0).
    - constructor; simpl; [split | ].
      + apply good_for_refresh.
        rewrite app_nil_r.
        now intros z Hz.
      + apply good_for_refresh_preserv.
        * intros z Hz; apply in_or_app; left.
          apply n2h_allvars; now apply in_or_app; left.
        * intros z Hz; inversion Hz.
        * now inversion H.
      + apply Forall_forall; intros C HC.
        apply good_for_refresh_preserv.
        * intros z Hz; apply in_or_app; right.
          revert HC; clear - Hz; induction l; intros Hin; inversion Hin; subst; simpl.
          -- apply in_or_app; left.
             apply n2h_allvars; now apply in_or_app; left.
          -- apply IHl in H.
             now apply in_or_app; right.
        * intros z Hz; inversion Hz.
        * inversion H; subst.
          now apply Forall_forall with (x:=C) in H3.
    - apply good_for_hilbert_rrefresh.
      + intros z Hz; simpl.
        clear - Hz.
        revert B Hz; induction l; simpl; intros B Hz.
        * now apply in_or_app; left.
        * apply IHl in Hz.
          apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz].
          -- simpl in Hz; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [right|left]; auto.
             now apply in_or_app; left.
          -- right; now apply in_or_app; right.
      + clear - H.
        revert B H; induction l; intros B HF; inversion HF; subst; simpl; auto.
        inversion H2; subst.
        apply IHl; constructor; auto.
        now split. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Ssequent | apply X ] | apply X0 ]; auto.
  now inversion Hg; inversion H2; constructor.
- assert ({rf : _ & Forall (rgood_for rf) (frl x A :: l) /\ rgood_for rf (subs x u A)
                  & hprove (n2h_sequent rf l (subs x u A)) -> hprove (n2h_sequent r l (subs x u A))})
    as [rf [Hg1 Hg2] Hp].
  { exists (rrefresh (hallvars (n2h_formula r (frl x A)))
                     (flat_map (fun C => hallvars (n2h_formula r C)) (subs x u A :: l)) r).
    - split; [ constructor; simpl | ].
      + apply (good_for_refresh _ (frl x A) _ (hallvars (n2h_formula r (frl x A)))).
        rewrite app_nil_r.
        now intros z Hz.
      + apply Forall_forall; intros C HC.
        apply (good_for_refresh_preserv (hallvars (n2h_formula r (frl x A)))).
        * intros z Hz.
          apply in_or_app; right.
          revert HC; clear - Hz; induction l; intros Hin; inversion Hin; subst; simpl.
          -- apply in_or_app; left.
             apply n2h_allvars; now apply in_or_app; left.
          -- apply IHl in H.
             now apply in_or_app; right.
        * intros z Hz; inversion Hz.
        * inversion H; subst.
          now apply Forall_forall with (x:=C) in H3.
      + apply good_for_refresh_preserv.
        * intros z Hz; apply in_or_app; left.
          apply n2h_allvars; now apply in_or_app; left.
        * intros z Hz; inversion Hz.
        * now inversion H.
    - remember (subs x u A) as B.
      apply good_for_hilbert_rrefresh.
      + intros z Hz; simpl.
        clear - Hz.
        revert B Hz; induction l; simpl; intros B Hz.
        * now apply in_or_app; left.
        * apply IHl in Hz.
          apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz].
          -- simpl in Hz; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [right|left]; auto.
             now apply in_or_app; left.
          -- right; now apply in_or_app; right.
      + clear - H.
        revert B H; induction l; intros B HF; inversion HF; subst; simpl; auto.
        inversion H2; subst.
        apply IHl; constructor; auto.
        now split. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply X ]; auto.
  rewrite n2h_subs with (lv:=x::nil); [ apply hprove_INST | | ].
  + apply lgood_hgood_closed with (lv := nil) (lv' := x :: nil); auto.
    * now constructor.
    * now inversion Hg1.
  + now constructor.
  + now inversion Hg1.
- auto.
- apply X.
  inversion H; destruct H2.
  now repeat constructor.
- remember (vfresh (flat_map (fun C => hallvars (n2h_formula r0 C)) (frl x A :: l))) as y.
  remember (rup (hvar y) r0) as r1.
  specialize X with r1.
  assert (Forall (rgood_for r1) (subs x (dvar 0) (fup 0 A) :: map (fup 0) l)) as pi'.
  { revert Heqy; inversion H; subst; intros Heqy.
    constructor.
    - simpl in H2; apply good_for_rup_subs with (x:=x) (y:=y) in H2.
      + rewrite <- (app_nil_l _) in H2; now apply lgood_for_less in H2.
      + now constructor.
      + intros Heq; inversion Heq; auto; subst x.
        apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl y A :: l)).
        now left.
      + intros Hin.
        apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl x A :: l)).
        rewrite <- Heqy; simpl; right.
        now apply in_or_app; left.
    - apply Forall_forall; intros B HB.
      apply in_map_iff in HB.
      destruct HB as [C [Heq HC]]; subst.
      apply Forall_forall with (x:=C) in H3; auto.
      now apply good_for_rup. }
  apply X in pi'.
  apply (hprove_GEN y) in pi'.
  assert (hprove (n2h_sequent r1 (map (fup 0) l) (frl y (subs x (tvar y) (fup 0 A))))) as pi''.
  { eapply hprove_MP; [ apply hprove_FRLsequent | ].
    - intros Hin.
      apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl x A :: l)).
      rewrite <- Heqy.
      simpl; apply in_cons.
      apply in_or_app; right.
      clear - Heqr1 Hin.
      revert Hin; induction l; simpl; intros Hin; auto.
      apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; auto.
      subst; rewrite n2h_rup in Hin.
      now apply hffreevars_hallvars.
    - enough (n2h_sequent r1 (map (fup 0) l) (subs x (dvar 0) (fup 0 A))
            = n2h_sequent r1 (map (fup 0) l) (subs x (tvar y) (fup 0 A))) as Heq
        by now rewrite <- Heq.
      remember (subs x (dvar 0) (fup 0 A)) as B.
      remember (subs x (tvar y) (fup 0 A)) as C.
      assert (n2h_formula r1 B = n2h_formula r1 C).
      { subst B C r1; clear; induction A; simpl; auto.
        - f_equal.
          rewrite ? map_map.
          apply map_ext; intros t.
          term_induction t.
        - f_equal; auto.
        - case_analysis; intuition.
          now rewrite IHA.
        - case_analysis; intuition.
          now rewrite IHA. }
      clear - H0; revert B C H0; induction l; simpl; intros B C Heq; auto.
      apply IHl; simpl; f_equal; auto. }
  remember (frl y (subs x (tvar y) (fup 0 A))) as B.
  remember (frl x A) as C.
  assert (hprove (n2h_formula r1 B ⟶ n2h_formula r0 C)) as pi'''.
  { subst B C; clear - H Heqr1 Heqy; simpl.
    eapply hprove_MP; [ apply hprove_FRL | ].
    + clear Heqy; simpl; intros Hin.
      apply in_remove in Hin; destruct Hin as [Hin Hneq].
      inversion H; subst.
      apply Hneq.
      revert Hin H2; clear; formula_induction A.
      * apply Forall_fold_right in H2.
        revert Hin H2; induction l; simpl; intros Hin HF; inversion HF; [inversion Hin | ]; subst.
        apply in_app_or in Hin; destruct Hin as [Hin|Hin].
        -- revert Hin H1; clear; term_induction a; intros Hin Hg.
           ++ inversion Hg; subst.
              now exfalso.
           ++ revert Hin; case_analysis; intuition.
           ++ apply Forall_fold_right in Hg.
              revert IHl Hin Hg; induction l; simpl; intros Hl Hin Hg.
              ** inversion Hin.
              ** inversion Hg; inversion Hl; subst.
                 apply in_app_or in Hin; destruct Hin as [Hin|Hin].
                 --- apply H5; auto.
                 --- apply IHl in H6; auto.
        -- apply IHl; auto.
      * apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
      * revert Hin; case_analysis; intros Hin; apply in_remove in Hin; destruct Hin.
        -- now exfalso; apply H0.
        -- apply IHA; auto.
           rewrite <- (app_nil_l _) in H2; now apply lgood_for_less in H2.
      * revert Hin; case_analysis; intros Hin; apply in_remove in Hin; destruct Hin.
        -- now exfalso; apply H0.
        -- apply IHA; auto.
           rewrite <- (app_nil_l _) in H2; now apply lgood_for_less in H2.
    + apply hprove_GEN.
      eapply hprove_CUT; [ apply hprove_INST with (t:=hvar x) | ]; simpl.
      * repeat constructor.
        assert (~ In y (hallvars (n2h_formula r1 (fup 0 A)))) as HA.
        { intros Hin.
          apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl x A :: l)).
          rewrite <- Heqy; simpl; right.
          apply in_or_app; left.
          now subst r1; rewrite n2h_rup in Hin. }
        revert HA; clear; formula_induction A.
        -- revert H; case_analysis; intros Hin.
           ++ exfalso; apply HA.
              apply in_remove in Hin; destruct Hin.
              now right; apply hffreevars_hallvars.
           ++ split; auto.
        -- revert H; case_analysis; intros Hin.
           ++ exfalso; apply HA.
              apply in_remove in Hin; destruct Hin.
              now right; apply hffreevars_hallvars.
           ++ split; auto.
      * enough (hfsubs y (hvar x) (n2h_formula r1 (subs x (tvar y) (fup 0 A))) = n2h_formula r0 A) as Heq
          by (rewrite Heq; apply hprove_I).
        rewrite n2h_subs with (lv:=x::nil); simpl.
        -- subst r1; rewrite n2h_rup.
           remember (n2h_formula r0 A) as B.
           assert (~ In y (hallvars B)) as HB.
           { intros Hin.
             apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl x A :: l)).
             rewrite <- Heqy.
             simpl; right.
             now subst; apply in_or_app; left. }
           revert HB; clear; formula_induction B.
           ++ assert (~ In y (hfreevars t)) by (intros Hin; apply HB; simpl; now apply in_or_app; left).
              revert H; clear; hterm_induction t; intros Hin.
              f_equal.
              rewrite <- (map_id l) at 2.
              apply map_ext_in; intros z Hz.
              apply Forall_forall with (x:=z) in IHl; auto.
              apply IHl.
              intros Hinz; apply Hin.
              revert Hz Hinz; clear; induction l; intros Hz Hinz; inversion Hz; subst; simpl.
              ** now apply in_or_app; left.
              ** apply in_or_app; right.
                 now apply IHl.
           ++ apply HB; simpl.
              now apply in_or_app; right.
           ++ repeat case_analysis; intuition; f_equal; intuition.
              apply nfree_hfsubs; simpl.
              intros Hin; apply H0.
              now apply hffreevars_hallvars.
           ++ repeat case_analysis; intuition; f_equal; intuition.
              apply nfree_hfsubs; simpl.
              intros Hin; apply H0.
              now apply hffreevars_hallvars.
         -- now constructor.
         -- subst r1; apply good_for_rup.
            now inversion H. }
  clear - Heqr1 pi'' pi'''.
  revert B C pi''' pi''; induction l; simpl; intros B C pBC pi.
  + eapply hprove_MP; eassumption.
  + apply IHl with (imp (fup 0 a) B); auto; simpl.
    subst r1; rewrite n2h_rup.
    eapply hprove_MP; [ apply hprove_B | apply pBC ].
- assert ({rf : _ & Forall (rgood_for rf) (exs x A :: l) /\ rgood_for rf (subs x u A)
                  & hprove (n2h_sequent rf l (exs x A)) -> hprove (n2h_sequent r0 l (exs x A))})
    as [rf [Hg1 Hg2] Hp].
  { exists (rrefresh (hallvars (n2h_formula r0 (subs x u A)))
                     (flat_map (fun C => hallvars (n2h_formula r0 C)) (exs x A :: l)) r0).
    - split; [ constructor; simpl | ].
      + apply good_for_refresh_preserv.
        * intros z Hz; right; apply in_or_app; left.
          apply n2h_allvars; now apply in_or_app; left.
        * intros z Hz; inversion Hz; [ now  constructor | now apply in_cons ].
        * now inversion H.
      + apply Forall_forall; intros C HC.
        apply (good_for_refresh_preserv (hallvars (n2h_formula r0 (subs x u A)))).
        * intros z Hz.
          right; apply in_or_app; right.
          revert HC; clear - Hz; induction l; intros Hin; inversion Hin; subst; simpl.
          -- apply in_or_app; left.
             apply n2h_allvars; now apply in_or_app; left.
          -- apply IHl in H.
             now apply in_or_app; right.
        * intros z Hz; inversion Hz.
        * inversion H; subst.
          now apply Forall_forall with (x:=C) in H3.
      + apply (good_for_refresh _ (subs x u A) _ (hallvars (n2h_formula r0 (subs x u A)))).
        rewrite app_nil_r.
        now intros z Hz.
    - remember (exs x A) as B.
      apply good_for_hilbert_rrefresh.
      + intros z Hz; simpl.
        clear - Hz.
        revert B Hz; induction l; simpl; intros B Hz.
        * now rewrite app_nil_r.
        * apply IHl in Hz.
          apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz].
          -- simpl in Hz; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [right|left]; auto.
             now apply in_or_app; left.
          -- right; now apply in_or_app; right.
      + clear - H.
        revert B H; induction l; intros B HF; inversion HF; subst; simpl; auto.
        inversion H2; subst.
        apply IHl; constructor; auto.
        now split. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply X ]; auto.
  + rewrite n2h_subs with (lv:=x::nil); [ apply hprove_EINST | | ].
    * apply lgood_hgood_closed with (lv := nil) (lv' := x :: nil); auto.
      -- now constructor.
      -- now inversion Hg1.
    * now constructor.
    * now inversion Hg1.
  + inversion Hg1; now constructor.
- remember (rrefresh (hallvars (n2h_formula r0 (exs x A)))
                     (flat_map (fun C => hallvars (n2h_formula r0 C)) (C :: l)) r0) as r1.
  assert (Forall (rgood_for r1) (C :: l)) as HgCl1.
  { remember (C :: l) as l'.
    remember (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) l') as lv.
    assert (incl lv lv) as Hincl by (now intros z Hz).
    rewrite Heqlv in Hincl at 1.
    clear - lv H Hincl Heqr1.
    revert H Hincl; induction l'; simpl; intros Hg Hincl; constructor;
      revert Heqr1; inversion Hg; subst; intros Heqr1.
    - subst; apply good_for_refresh_preserv; auto.
      + intros z Hz; apply Hincl.
        apply in_or_app; left.
        apply n2h_allvars.
        now apply in_or_app; left.
      + intros z Hz; inversion Hz.
    - apply IHl'; auto.
      intros z Hz; apply Hincl.
      now apply in_or_app; right. }
  assert (rgood_for r1 C) as HgC1 by (now inversion HgCl1).
  assert (Forall (rgood_for r1) l) as Hgl1 by (now inversion HgCl1); clear HgCl1.
  assert (rgood_for r1 (exs x A)) as HgA1
    by (subst; apply good_for_refresh; rewrite app_nil_r; now intros z Hz).
  apply good_for_hilbert_rrefresh with (l:=hallvars (n2h_formula r0 (exs x A)))
                                       (ld:=flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (C :: l)).
  + clear; revert C; induction l; simpl; intros C.
    * rewrite app_nil_r; now intros z Hz.
    * intros z Hz; apply IHl in Hz; simpl in Hz.
      apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz].
      -- apply in_app_or in Hz; destruct Hz as [Hz|Hz]; auto.
         right; now apply in_or_app; left.
      -- right; now apply in_or_app; right.
  + clear - H; revert C H; induction l; simpl; intros C Hg; inversion Hg; subst; auto.
    inversion H2; subst.
    apply IHl; constructor; simpl; auto.
  + rewrite <- Heqr1.
    eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Ssequent | ] | apply X; constructor; auto ].
    apply hprove_imp_sequent.
    remember (vfresh (flat_map (fun C => hallvars (n2h_formula r1 C)) (exs x A :: C :: l))) as y.
    assert (hprove (hexs x (n2h_formula r1 A) ⟶ hexs y (hfsubs x (hvar y) (n2h_formula r1 A)))) as pi'.
    { simpl in Heqy.
      remember (n2h_formula r1 A) as B; clear - Heqy.
      assert (~ In y (hallvars B)) as Hf.
      { intros Hin.
        apply vfresh_prop with (x:: hallvars B ++
             hallvars (n2h_formula r1 C) ++ flat_map (fun C : formula => hallvars (n2h_formula r1 C)) l).
        rewrite <- Heqy; simpl; right.
        now apply in_or_app; left. }
      clear Heqy.
      eapply hprove_MP; [ apply hprove_EXS | ].
      - simpl; intros Hin.
        apply in_remove in Hin; destruct Hin as [Hin _].
        apply hffreevars_subs in Hin; destruct Hin as [Hin|Hin].
        + simpl in Hin; destruct Hin as [Heq Hin]; destruct Heq; auto; subst.
          now apply Hf, hffreevars_hallvars.
        + now destruct Hin.
      - apply hprove_GEN.
        replace (B ⟶ hexs y (hfsubs x (hvar y) B))
           with (hfsubs y (hvar x) (hfsubs x (hvar y) B) ⟶ hexs y (hfsubs x (hvar y) B)).
        + apply hprove_EINST.
          simpl; repeat constructor.
          revert Hf; formula_induction B.
          * case_analysis.
            -- exfalso.
               rewrite eqb_refl in H.
               apply in_remove in H; destruct H.
               apply Hf; right; apply hffreevars_hallvars; assumption.
            -- split; auto.
          * case_analysis.
            -- exfalso.
               rewrite eqb_refl in H.
               apply in_remove in H; destruct H.
               apply Hf; right; apply hffreevars_hallvars; assumption.
            -- split; auto.
        + f_equal.
          now apply hbisubs. }
    simpl; eapply hprove_CUT; [ apply pi' | ].
    eapply hprove_MP; [ apply hprove_EXS | ].
    * intros Hin.
      apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r1 C)) (exs x A :: C :: l)).
      rewrite <- Heqy.
      simpl; right; apply in_or_app; right.
      clear - Hin; revert C Hin; induction l; simpl; intros C Hin.
      -- rewrite app_nil_r; apply n2h_allvars.
         now apply in_or_app; right.
      -- apply IHl in Hin; simpl in Hin.
         apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
         ++ apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
            right; now apply in_or_app; left.
         ++ right; now apply in_or_app; right.
    * apply hprove_GEN.
      replace (hvar y) with (n2h_term r1 (tvar y)) by reflexivity.
      rewrite <- n2h_subs with (lv:=x::nil); auto; [ | now constructor ].
      apply hprove_sequent_imp.
      remember (rup (hvar y) r1) as r2.
      assert (Forall (rgood_for r2) (fup 0 C :: subs x (dvar 0) (fup 0 A) :: map (fup 0) l)) as pi.
      { constructor; [ | constructor ]; subst r2.
        - now apply good_for_rup.
        - simpl in HgA1; apply good_for_rup_subs with (x:=x) (y:=y) in HgA1.
          + rewrite <- (app_nil_l _) in HgA1; now apply lgood_for_less in HgA1.
          + now constructor.
          + intros Heq; inversion Heq; auto; subst x.
            apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r1 C)) (exs y A :: C :: l)).
            now left.
          + intros Hin.
            apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r1 C)) (exs x A :: C :: l)).
            rewrite <- Heqy; simpl; right.
            now apply in_or_app; left.
        - apply Forall_forall; intros E HE.
          apply in_map_iff in HE; destruct HE as [E' [Heq HE]]; subst E.
          apply Forall_forall with (x:=E') in Hgl1; auto.
          now apply good_for_rup. }
      apply X0 in pi; simpl in pi.
      remember (imp (subs x (dvar 0) (fup 0 A)) (fup 0 C)) as B.
      remember (imp (subs x (tvar y) A) C) as D.
      assert (hprove (n2h_formula r2 B ⟶ n2h_formula r1 D)) as HBD.
      { subst B D r2; simpl; rewrite ? n2h_rup.
        rewrite n2h_rup_subs with (lv:=x::nil); auto.
        - enough (n2h_formula r1 (subs x (tvar y) A) = hfsubs x (hvar y) (n2h_formula r1 A))
            as Heq by (rewrite Heq; apply hprove_I).
          apply n2h_subs with (x :: nil); auto.
          now constructor.
        - now constructor. }
      clear - Heqr2 pi HBD; revert B D pi HBD; induction l; simpl; intros B D pi HBD.
      -- eapply hprove_MP; eassumption.
      -- apply IHl with (imp (fup 0 a) B); auto.
         simpl; subst.
         rewrite n2h_rup.
         eapply hprove_MP; [ apply hprove_B | apply HBD ].
Qed.

Proposition n2h_closed : forall r, (forall n, hclosed (r n)) ->
  forall A, prove nil A -> hprove (n2h_formula r A).
Proof.
intros r Hc A pi.
apply normalization in pi.
change (n2h_formula r A) with (n2h_sequent r nil A).
apply n2h; [ assumption | ].
apply Forall_forall; intros.
now apply lgood_for_closed.
Qed.

End N2H.

