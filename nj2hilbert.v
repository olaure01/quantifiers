(* From Natural Deduction to Hilbert System *)

Require Import stdlib_more.
Require Export nj1 hilbert.


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
  induction A as [ XX ll | A1 ? A2 ? | xx A | xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try f_equal; try (induction ll as [ | tt lll IHll ]; simpl; intuition;
                      rewrite IHll; f_equal; intuition)
  | try (f_equal; intuition)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail) ];
  try (now (rnow idtac)); try (now rcauto).

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
  | intros cc ll IHll; simpl;
    rewrite ? flat_map_concat_map; rewrite ? map_map;
    try f_equal;
    try (apply map_ext_in; intros i Hi; specialize_Forall_all i);
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i);
    try (now intuition) ];
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


Section Fixed_r.

Variable r : nat -> hterm.

(* Capture-avoiding property *)
Fixpoint ltgood_for lv (t : term) :=
match t with
| dvar n => Forall (fun x => ~ In x (hfreevars (r n))) lv
| tvar x => True
| tconstr f l => fold_right (fun x P => and (ltgood_for lv x) P) True l
end.

Lemma ltgood_for_less : forall x lv1 lv2 t,
  ltgood_for (lv1 ++ x :: lv2) t -> ltgood_for (lv1 ++ lv2) t.
Proof. term_induction t; intros HF.
- apply Forall_incl with (lv1 ++ x :: lv2); intuition.
- apply Forall_fold_right in HF.
  apply Forall_fold_right, Forall_forall; intros u Hu.
  specialize_Forall_all u; intuition.
Qed.

Lemma ltgood_for_closed : forall l t, (forall n, hclosed (r n)) -> ltgood_for l t.
Proof. intros l t Hc; term_induction t.
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

Lemma lgood_for_less : forall x lv1 lv2 A,
  lgood_for (lv1 ++ x :: lv2) A -> lgood_for (lv1 ++ lv2) A.
Proof. intros x lv1 lv2 A; revert lv1 lv2; formula_induction A.
- apply Forall_fold_right in H; apply Forall_fold_right.
  eapply Forall_impl; [ apply ltgood_for_less | eassumption ].
- now rewrite app_comm_cons in H; apply IHA in H.
- now rewrite app_comm_cons in H; apply IHA in H.
Qed.

Lemma lgood_for_closed : forall l A, (forall n, hclosed (r n)) -> lgood_for l A.
Proof. intros l A Hc; revert l; formula_induction A.
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
revert IHl Hin; induction l; simpl; intros Hl Hin; auto.
inversion Hl; subst; in_solve.
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
- specialize_Forall Hg with x.
  symmetry; now apply nfree_htsubs.
- apply Forall_fold_right in Hg.
  f_equal; apply map_ext_in; intros a Hina.
  now specialize_Forall_all a; apply (IHl _ Hin).
Qed.

Lemma n2h_subs : forall x u A lv, In x lv -> lgood_for lv A ->
  n2h_formula (subs x u A) = hfsubs x (n2h_term u) (n2h_formula A).
Proof. formula_induction A.
- now simpl in H0; apply n2h_tsubs with lv.
- now simpl in H0.
- now apply IHA1 with lv.
- now apply IHA2 with lv.
- case_analysis; [ reflexivity | ].
  rewrite <- (app_nil_l _) in H0; apply lgood_for_less in H0.
  now f_equal; apply IHA with lv.
- case_analysis; [ reflexivity | ].
  rewrite <- (app_nil_l _) in H0; apply lgood_for_less in H0.
  now f_equal; apply IHA with lv.
Qed.

Lemma n2h_allvars : forall A,
  incl (allvars A ++ hffreevars (n2h_formula A)) (hallvars (n2h_formula A)).
Proof. formula_induction A; simpl; intros z Hin; try in_solve.
- revert Hin; induction l; simpl; intros Hin; try in_solve.
  apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition.
  now apply n2h_hfreevars.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  inversion_clear Hin; subst; intuition.
  apply in_cons, IHA.
  apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right]; auto.
  now apply in_remove in H.
Qed.


(* Properties relating [lgood_for] and [n2h] *)
Lemma ltgood_for_nfree : forall y l u,
  closed u -> In y l -> ltgood_for l u -> ~ In y (hfreevars (n2h_term u)).
Proof. intros y l u; revert l; term_induction u; intros lv Hc Hinl Hg Hinu.
- specialize_Forall Hg with y; intuition.
- apply concat_is_nil in Hc.
  apply Forall_fold_right in Hg.
  apply in_flat_map in Hinu; destruct Hinu as [z [Hinzl Hinz]].
  apply in_map_iff in Hinzl.
  destruct Hinzl as [v [Heq Hz]]; subst.
  specialize_Forall_all v.
  apply in_map with (f:= freevars) in Hz.
  specialize_Forall Hc with (freevars v).
  apply IHl in Hg; intuition.
Qed.

Lemma ltgood_for_freevars : forall x l t, In x l -> ltgood_for l t ->
  In x (hfreevars (n2h_term t)) -> In x (freevars t).
Proof. intros x l t; revert l; term_induction t; intros lv Hinlv Hg Hin.
- now specialize_Forall Hg with x.
- apply Forall_fold_right in Hg.
  apply in_flat_map_Exists in Hin; apply Exists_exists in Hin.
  destruct Hin as [lv2 [Hlv2in Hinlv2]].
  apply in_map_iff in Hlv2in; destruct Hlv2in as [u [Heq Hinu]]; subst.
  specialize_Forall_all u.
  apply IHl with lv in Hinlv2; intuition.
  rewrite <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
Qed.

Lemma ltgood_for_nfree_subs : forall x y l u t,
  closed u -> In y l -> ltgood_for l (tsubs x u t) ->
  In y (hfreevars (n2h_term u)) -> In x (freevars t) -> False.
Proof. intros x y l u t; revert l; term_induction t; intros lv Hc Hinl Hg Hinu Hint.
- destruct Hint; subst; intuition.
  revert Hg; case_analysis; intros Hg.
  now apply ltgood_for_nfree with (y:= y) in Hg.
- apply Forall_fold_right in Hg.
  apply in_flat_map in Hint; destruct Hint as [z [Hinzl Hinz]].
  apply in_map_iff in Hinzl.
  destruct Hinzl as [v [Heq Hz]]; subst.
  specialize_Forall_all v.
  apply in_map with (f:= tsubs x u) in Hz.
  specialize_Forall Hg with (tsubs x u v).
  apply IHl in Hg; intuition.
Qed.

Lemma lgood_for_nfree_subs : forall x y l u A,
  closed u -> In y l -> lgood_for l (subs x u A) ->
  In y (hfreevars (n2h_term u)) -> In x (ffreevars A) -> False.
Proof. intros x y l u A; revert l; formula_induction A.
- apply Forall_fold_right in H1.
  apply in_flat_map in H3; destruct H3 as [z [Hinzl Hinz]].
  apply in_map with (f:= tsubs x u) in Hinzl.
  specialize_Forall H1 with (tsubs x u z).
  apply ltgood_for_nfree_subs with (y:= y) in H1; intuition.
- apply in_app_or in H3; destruct H3.
  + now apply IHA1 with l.
  + now apply IHA2 with l.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  apply in_remove in H3; destruct H3 as [Hin Hneq].
  revert H1; case_analysis; intros Hg; intuition.
  rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; simpl in Hg.
  apply IHA in Hg; intuition.
Qed.

Lemma lgood_for_ffreevars : forall x l A, In x l -> lgood_for l A ->
  In x (hffreevars (n2h_formula A)) -> In x (ffreevars A).
Proof. intros x l A; revert l; formula_induction A.
- apply in_flat_map in H1; destruct H1 as [t [Htin Hint]].
  apply in_map_iff in Htin; destruct Htin as [y [Heq Hiny]]; subst.
  apply Forall_fold_right in H0; specialize_Forall H0 with y.
  apply ltgood_for_freevars with (l:= l0) in Hint; intuition.
  rewrite <- flat_map_concat_map; apply in_flat_map; exists y; intuition.
- apply in_or_app; apply in_app_or in H1; destruct H1; [left|right].
  + now apply IHA1 with l.
  + now apply IHA2 with l.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  apply in_remove in H1; destruct H1 as [Hin Hneq].
  apply notin_remove; intuition.
  apply IHA with (x0 :: l); intuition.
Qed.

Lemma lgood_hgood_closed : forall u x lv lv' A,
  closed u -> lgood_for lv (subs x u A) -> In x lv' -> lgood_for lv' A ->
  Forall (fun y => hgood_for x y (n2h_formula A)) (hfreevars (n2h_term u)).
Proof. intros u x lv lv' A; revert lv; formula_induction A.
- now apply Forall_forall.
- apply Forall_and.
  + now apply IHA1 with lv.
  + now apply IHA2 with lv.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  revert H0; case_analysis; intros H0.
  + apply Forall_forall; intros z Hz Hin.
    exfalso; now apply in_remove in Hin.
  + rewrite <- (app_nil_l _) in H2; apply lgood_for_less in H2; simpl in H2.
    assert (Hg := H0).
    apply IHA in H0; auto.
    apply Forall_forall; intros z Hz Hin.
    specialize_Forall H0 with z; split; [ assumption | ].
    intros Heq2; subst.
    apply in_remove in Hin; destruct Hin as [Hin _].
    apply lgood_for_ffreevars with (l:= lv') in Hin; intuition.
    apply lgood_for_nfree_subs with (y:= x0) in Hg; intuition.
Qed.


(* Turn sequents into formulas *)
Definition s2f l (A : formula) := fold_left (fun x y => imp y x) l A.

Lemma good_for_s2f : forall lv l A, lgood_for lv (s2f l A) <-> Forall (lgood_for lv) (A :: l).
Proof.
induction l; simpl; intros A; split; intros Hg; intuition.
- inversion_clear Hg; intuition.
- apply IHl in Hg; inversion_clear Hg as [ | ? ? Hi Hl]; simpl in Hi; intuition.
- apply IHl; inversion_clear Hg as [ | ? ? Hi Hl]; inversion_clear Hl; constructor; simpl; intuition.
Qed.

Notation n2h_sequent l A := (n2h_formula (s2f l A)).

Lemma n2h_sequent_allvars : forall l A,
  incl (hallvars (n2h_sequent l A))
       (hallvars (n2h_formula A) ++ flat_map (fun C => hallvars (n2h_formula C)) l).
Proof. induction l; simpl; intros A C HC; intuition; apply IHl in HC; in_solve. Qed.

Lemma hprove_Bsequent : forall l A B,
  hprove ((n2h_formula A ⟶ n2h_formula B) ⟶ n2h_sequent l A ⟶ n2h_sequent l B).
Proof.
induction l; simpl; intros A B.
- apply hprove_I.
- specialize IHl with (imp a A) (imp a B); simpl in IHl.
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
specialize IHl2 with l1 (imp a A); apply IHl2.
eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_K ] | apply pi ].
Qed.

Lemma hprove_Ssequent : forall l A B,
  hprove (n2h_sequent l (imp A B) ⟶ n2h_sequent l A ⟶ n2h_sequent l B).
Proof.
induction l; simpl; intros A B.
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
  + intros Hin; apply Hf; in_solve.
  + eapply hprove_MP; [ apply hprove_Bsequent | ]; simpl.
    apply hprove_FRL.
    intros Hin; apply Hf; in_solve.
Qed.

End Fixed_r.


Notation n2h_sequent r l A := (n2h_formula r (s2f l A)).
Notation rgood_for r := (lgood_for r nil).

Definition rsubs x y (r : nat -> hterm) n := htsubs x (hvar y) (r n).

Lemma hfreevars_rsubs : forall x y r n z,
  In z (hfreevars (rsubs x y r n)) -> (z = y /\ In x (hfreevars (r n))) \/ (In z (hfreevars (r n)) /\ z <> x).
Proof. unfold rsubs; intros x y r n z Hin; apply hfreevars_tsubs in Hin; simpl in Hin; in_solve. Qed.

Lemma hfreevars_n2h_rsubs : forall x y r t z,
  In z (hfreevars (n2h_term (rsubs x y r) t)) -> z = y \/ In z (hfreevars (n2h_term r t)).
Proof. term_induction t; intros z Hin.
- apply hfreevars_rsubs in Hin; intuition.
- rewrite <- flat_map_concat_map in Hin.
  apply in_flat_map in Hin; destruct Hin as [u [Huin Hinu]].
  specialize_Forall IHl with u; apply IHl in Hinu.
  destruct Hinu as [Hinu|Hinu]; [left; assumption | right].
  rewrite <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
Qed.

Lemma hfreevars_n2h_rsubs_self : forall x y r t lv,
  In x lv -> ltgood_for r lv t -> ~ In y (freevars t) ->
  In y (hfreevars (n2h_term (rsubs x y r) t)) -> In y (hfreevars (n2h_term r t)).
Proof. term_induction t; intros lv Hlv Hg Hnin Hin.
- apply hfreevars_rsubs in Hin; destruct Hin as [Hin|Hin]; intuition.
  specialize_Forall Hg with x; intuition.
- apply Forall_fold_right in Hg.
  apply in_flat_map in Hin; destruct Hin as [u [Huin Hinu]].
  apply in_map_iff in Huin; destruct Huin as [v [Heq Hv]]; subst.
  specialize_Forall_all v; apply IHl in Hg; intuition.
  + rewrite <- flat_map_concat_map; apply in_flat_map; exists v; intuition.
  + apply Hnin.
    rewrite <- flat_map_concat_map; apply in_flat_map; exists v; intuition.
Qed.

Lemma hffreevars_n2h_rsubs_self : forall x y r A lv,
  In x lv -> lgood_for r lv A -> ~ In y (ffreevars A) ->
  In y (hffreevars (n2h_formula (rsubs x y r) A)) -> In y (hffreevars (n2h_formula r A)).
Proof. formula_induction A.
- apply Forall_fold_right in H0.
  apply in_flat_map in H2; destruct H2 as [u [Huin Hinu]].
  apply in_map_iff in Huin; destruct Huin as [v [Heq Hv]]; subst.
  specialize_Forall_all v.
  apply hfreevars_n2h_rsubs_self with (lv:= lv) in Hinu; intuition.
  + rewrite map_map, <- flat_map_concat_map; apply in_flat_map; exists v; intuition.
  + apply H1.
    apply in_flat_map; exists v; intuition.
- apply in_or_app; apply in_app_or in H2; destruct H2 as [Hin|Hin]; [left|right].
  + apply IHA1 with lv in Hin; intuition.
  + apply IHA2 with lv in Hin; intuition.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  apply in_remove in H2; destruct H2 as [Hin Hneq]; apply notin_remove; intuition.
  apply IHA with lv; intuition.
  + rewrite <- (app_nil_l _) in H0; now apply lgood_for_less in H0.
  + apply H1; apply notin_remove; intuition.
Qed.

Lemma hallvars_n2h_rsubs : forall x y r A z,
  In z (hallvars (n2h_formula (rsubs x y r) A)) -> z = y \/ In z (hallvars (n2h_formula r A)).
Proof. formula_induction A.
- apply in_flat_map in H; destruct H as [u [Huin Hinu]].
  rewrite map_map in Huin.
  apply in_map_iff in Huin; destruct Huin as [v [Heq Hv]]; subst.
  apply hfreevars_n2h_rsubs in Hinu.
  destruct Hinu as [Hinu|Hinu]; [left; intuition | right].
  rewrite map_map, <- flat_map_concat_map; apply in_flat_map; exists v; intuition.
- apply in_app_or in H; destruct H as [Hin|Hin].
  + apply IHA1 in Hin; intuition.
  + apply IHA2 in Hin; intuition.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  intuition.
  apply IHA in H0; intuition.
Qed.

Lemma tgood_for_fresh : forall r y x t lv, ~ In y (freevars t ++ lv) ->
  ltgood_for r lv t -> ltgood_for (rsubs x y r) lv t.
Proof.
term_induction t; intros lv Hin Hg.
- apply Forall_forall; intros z Hz Hinz.
  specialize_Forall Hg with z; apply Hg.
  apply hfreevars_rsubs in Hinz; intuition; subst; intuition.
- apply Forall_fold_right; apply Forall_fold_right in Hg.
  apply Forall_forall; intros u Hu.
  specialize_Forall_all u.
  apply IHl; intuition.
  apply in_map with (f:= freevars) in Hu.
  apply Hin.
  apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right]; intuition.
  now apply in_flat_map; exists (freevars u).
Qed.

Lemma good_for_fresh : forall r y x A lv, ~ In y (allvars A ++ lv) ->
  lgood_for r lv A -> lgood_for (rsubs x y r) lv A.
Proof. formula_induction A.
- apply Forall_fold_right in H0; apply Forall_fold_right.
  apply Forall_forall; intros u Hu.
  specialize_Forall H0 with u.
  apply tgood_for_fresh; intuition.
  apply H.
  apply in_or_app; apply in_app_or in H1; destruct H1 as [H1|H1]; [left|right]; intuition.
  now apply in_flat_map; exists u.
- apply IHA1; intuition.
  apply H; in_solve.
- apply IHA2; intuition.
  apply H; in_solve.
- apply IHA; intuition.
  apply in_app_or in H1; destruct H1 as [H1|H1]; try inversion H1; intuition; in_solve.
- apply IHA; intuition.
  apply in_app_or in H1; destruct H1 as [H1|H1]; try inversion H1; intuition; in_solve.
Qed.


(* Freshness function now required *)

(* update [r] by refreshing all variables from [l] in the target *)
(* generated variables are moreover chosen fresh with respect to [ld] *)
Fixpoint rrefresh l ld r :=
match l with
| nil => r
| x :: tl => let y := vfresh (l ++ ld) in rrefresh tl (x :: y :: ld) (rsubs x y r)
end.

Lemma hfreevars_rrefresh : forall n l ld r z,
  In z (l ++ ld) -> In z (hfreevars (rrefresh l ld r n)) -> In z (hfreevars (r n)).
Proof.
induction l; intros ld r z Hinz Hin; simpl in Hin; auto.
apply IHl in Hin; intuition; try in_solve.
apply hfreevars_rsubs in Hin; destruct Hin as [Hin|Hin]; intuition.
exfalso; subst.
apply vfresh_prop with (a :: l ++ ld); in_solve.
Qed.

Lemma rrefresh_notin : forall n z lvA lv r,
  In z (hfreevars (rrefresh lvA lv r n)) -> ~ In z lvA.
Proof.
induction lvA; simpl; intros lv r Hinf Hin; inversion Hin; subst; simpl in Hin.
- apply hfreevars_rrefresh in Hinf; try in_solve.
  apply hfreevars_rsubs in Hinf; destruct Hinf as [[Hinf _]|Hinf]; [ | intuition ].
  apply vfresh_prop with (z :: lvA ++ lv); rewrite <- Hinf; now constructor.
- now apply IHlvA in Hinf.
Qed.

Lemma good_for_refresh_preserv : forall l r ld lv A, incl (allvars A ++ lv) ld ->
  lgood_for r lv A -> lgood_for (rrefresh l ld r) lv A.
Proof.
induction l; intros r ld lv A Hld Hg; simpl; auto.
apply IHl; try (intros; in_solve).
apply good_for_fresh; auto; intros Hin.
apply vfresh_prop with (a :: l ++ ld).
apply Hld in Hin; in_solve.
Qed.

Lemma tgood_for_refresh : forall ld t r lvt lv, incl (hfreevars (n2h_term r t) ++ lv) lvt ->
  ltgood_for (rrefresh lvt ld r) lv t.
Proof. term_induction t; intros r lvt lv Hincl.
- apply Forall_forall; intros z Hz Hinz.
  apply rrefresh_notin in Hinz; apply Hinz; in_solve.
- apply Forall_fold_right.
  apply Forall_forall; intros u Hu.
  specialize_Forall IHl with u; apply IHl.
  intros z Hz; apply Hincl.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; intuition.
  apply in_map with (f:= fun x => hfreevars (n2h_term r x)) in Hu.
  now rewrite flat_map_concat_map, map_map; apply in_flat_map; exists (hfreevars (n2h_term r u)).
Qed.

Lemma good_for_refresh : forall ld A r lvA lv, incl (hallvars (n2h_formula r A) ++ lv) lvA ->
  lgood_for (rrefresh lvA ld r) lv A.
Proof. formula_induction A; 
  (try apply IHA1); (try apply IHA2); (try apply IHA); try (intros z Hz; apply H; in_solve).
apply Forall_fold_right.
apply Forall_forall; intros u Hu.
apply tgood_for_refresh.
intros z Hz; apply H.
apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; intuition.
apply in_map with (f:= fun x => hfreevars (n2h_term r x)) in Hu.
rewrite map_map; apply in_flat_map; exists (hfreevars (n2h_term r u)); intuition.
Qed.

Lemma bitsubs_fresh : forall r y x t,
  ~ In y (freevars t ++ hfreevars (n2h_term r t)) ->
  htsubs y (hvar x) (n2h_term (rsubs x y r) t) = n2h_term r t.
Proof. term_induction t; intros Hnin.
- now unfold rsubs; apply htbisubs.
- f_equal.
  apply map_ext_in; intros u Hinu.
  specialize_Forall IHl with u; apply IHl; intros Hin; apply Hnin.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right].
  + apply in_map with (f:= freevars) in Hinu; now apply in_flat_map; exists (freevars u).
  + apply in_map with (f:= fun x => hfreevars (n2h_term r x)) in Hinu;
      now apply in_flat_map; exists (hfreevars (n2h_term r u)).
Qed.

Lemma bisubs_fresh : forall r y x A,
  ~ In y (allvars A ++ hffreevars (n2h_formula r A)) ->
  hfsubs y (hvar x) (n2h_formula (rsubs x y r) A) = n2h_formula r A.
Proof. formula_induction A.
- apply bitsubs_fresh; intros Hin; apply H; in_solve.
- apply H; in_solve.
- apply IHA1; intros Hin; apply H; in_solve.
- apply IHA2; intros Hin; apply H; in_solve.
- f_equal; case_analysis; intuition.
  apply IHA; intros Hin; apply H1.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition.
  apply notin_remove; intuition.
- f_equal; case_analysis; intuition.
  apply IHA; intros Hin; apply H1.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition.
  apply notin_remove; intuition.
Qed.

Lemma good_for_hilbert_rsubs : forall r y x A,
  ~ In y (allvars A ++ hffreevars (n2h_formula r A)) -> rgood_for r A ->
  hprove (n2h_formula (rsubs x y r) A) -> hprove (n2h_formula r A).
Proof.
intros r y x A Hnin Hg pi.
rewrite <- bisubs_fresh with (x:=x) (y:=y); auto.
eapply hprove_MP; [ apply hprove_INST | apply hprove_GEN ]; auto.
simpl; repeat constructor.
revert Hnin Hg; clear; induction A; simpl; intros; trivial.
- split.
  + apply IHA1; intuition; apply Hnin; in_solve.
  + apply IHA2; intuition; apply Hnin; in_solve.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  split.
  + apply IHA; intuition.
    * apply H2.
      apply in_or_app; apply in_app_or in H0; destruct H0 as [Hin|Hin]; [left|right]; intuition.
      apply notin_remove; intuition.
    * rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
  + intros Heq; subst.
    apply Hnin; right.
    apply in_or_app; right.
    apply in_remove in H; destruct H as [Hin Hneq]; apply notin_remove; intuition.
    apply hffreevars_n2h_rsubs_self with (lv:= c :: nil) in Hin; intuition.
    apply H0, in_or_app; left.
    now apply ffreevars_allvars.
Qed.

Lemma good_for_hilbert_rrefresh : forall l r ld A,
  incl (hallvars (n2h_formula r A)) ld -> rgood_for r A ->
  hprove (n2h_formula (rrefresh l ld r) A) -> hprove (n2h_formula r A).
Proof.
induction l; intros r ld A HA Hg pi; simpl; auto.
apply IHl in pi.
- apply good_for_hilbert_rsubs in pi; auto.
  intros Hin.
  apply vfresh_prop with (a :: l ++ ld).
  assert (Hincl := n2h_allvars r A).
  apply Hincl, HA in Hin; in_solve.
- intros z Hz.
  apply hallvars_n2h_rsubs in Hz; intuition; subst; intuition.
- apply good_for_fresh; auto.
  rewrite app_nil_r; intros Hin.
  apply vfresh_prop with (a :: l ++ ld).
  assert (Ha := n2h_allvars r A).
  eapply or_introl in Hin; apply in_or_app, Ha, HA in Hin; in_solve.
Qed.


Definition rup t r n : hterm :=
match n with
| 0 => t
| S k => r k
end.

Lemma tgood_for_rup : forall t r u lv,
  ltgood_for r lv u -> ltgood_for (rup t r) lv (tup 0 u).
Proof. term_induction u; intros lv HF.
apply Forall_fold_right in HF; apply Forall_fold_right.
apply Forall_forall; intros z Hz.
apply in_map_iff in Hz; destruct Hz as [y [Heq Hy]]; subst.
specialize_Forall_all y; auto.
Qed.

Lemma good_for_rup : forall t r A lv,
  lgood_for r lv A -> lgood_for (rup t r) lv (fup 0 A).
Proof. formula_induction A.
apply Forall_fold_right in H; apply Forall_fold_right.
apply Forall_forall; intros u Hu.
apply in_map_iff in Hu; destruct Hu as [v [Heq Hv]]; subst.
specialize_Forall H with v.
now apply tgood_for_rup.
Qed.

Lemma good_for_rup_tsubs : forall r x y lv t,
  ~ In y lv -> ~ In y (hfreevars (n2h_term r t)) ->
  ltgood_for r lv t ->  ltgood_for (rup (hvar y) r) lv (tsubs x (dvar 0) (tup 0 t)).
Proof. term_induction t; intros Hlv Hy Hg.
- case_analysis; intuition.
  apply Forall_forall; intros z Hz; intros Heqz; intuition; subst; intuition.
- apply Forall_fold_right; apply Forall_fold_right in Hg.
  apply Forall_forall; intros z Hz.
  apply in_map_iff in Hz; destruct Hz as [z' [Heq Hz]]; subst.
  specialize_Forall_all z'.
  apply IHl; intuition.
  apply Hy.
  rewrite <- flat_map_concat_map; apply in_flat_map; exists z'; intuition.
Qed.

Lemma good_for_rup_subs : forall r x y A lv,
  In x lv -> ~ In y lv -> ~ In y (hallvars (n2h_formula r A)) ->
  lgood_for r lv A ->  lgood_for (rup (hvar y) r) lv (subs x (dvar 0) (fup 0 A)).
Proof. formula_induction A;
try rename H into Hxlv; try rename H0 into Hylv; try rename H1 into Hyl; try rename H2 into Hg.
- apply Forall_fold_right in Hg; apply Forall_fold_right.
  rewrite map_map; apply Forall_forall; intros u Hu.
  apply in_map_iff in Hu; destruct Hu as [v [Heq Hv]]; subst.
  specialize_Forall Hg with v.
  apply good_for_rup_tsubs; intuition.
  apply Hyl.
  rewrite map_map, <- flat_map_concat_map; apply in_flat_map; exists v; intuition.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  case_analysis.
  + now apply good_for_rup.
  + apply IHA; intuition.
    apply Hylv.
    destruct H as [Hin|Hin]; subst; intuition.
Qed.

Lemma n2h_rup_term : forall t u r, n2h_term (rup t r) (tup 0 u) = n2h_term r u.
Proof. term_induction u; intros r; f_equal.
rewrite map_map; apply map_ext_in; intros v Hv.
now specialize_Forall IHl with v.
Qed.

Lemma n2h_rup : forall t A r, n2h_formula (rup t r) (fup 0 A) = n2h_formula r A.
Proof. formula_induction A; apply n2h_rup_term. Qed.

Lemma n2h_rup_subs : forall x lv t A r, In x lv -> lgood_for r lv A ->
  n2h_formula (rup t r) (subs x (dvar 0) (fup 0 A)) = hfsubs x t (n2h_formula r A).
Proof.
intros; rewrite n2h_subs with (lv:=lv); auto.
- f_equal; apply n2h_rup.
- now apply good_for_rup.
Qed.

Proposition n2h : forall l A,
  prove l A -> forall r, Forall (rgood_for r) (A :: l) -> hprove (n2h_sequent r l A).
Proof.
intros l A pi; induction pi; intros r Hg.
- apply hprove_Ksequent, hprove_K2sequent.
- apply IHpi.
  inversion_clear Hg as [ | ? ? Hg1 Hgl]; destruct Hg1; intuition.
- assert ({rf : _ & Forall (rgood_for rf) (imp A B :: l)
                  & hprove (n2h_sequent rf l B) -> hprove (n2h_sequent r l B)})
    as [rf Hg' Hp].
  { exists (rrefresh (hallvars (n2h_formula r A))
                     (flat_map (fun C => hallvars (n2h_formula r C)) (B :: l)) r).
    - constructor; simpl; [split | ].
      + apply good_for_refresh.
        rewrite app_nil_r; apply incl_refl.
      + apply good_for_refresh_preserv.
        * rewrite app_nil_r; intros z Hz.
          assert (Ha := n2h_allvars r B); in_solve.
        * now inversion Hg.
      + apply Forall_forall; intros C HC.
        apply good_for_refresh_preserv.
        * rewrite app_nil_r; intros z Hz.
          assert (Ha := n2h_allvars r C).
          apply in_or_app; right.
          apply in_flat_map; exists C; intuition.
        * inversion Hg as [ | ? ? _ Hgl].
          now specialize_Forall Hgl with C.
    - apply good_for_hilbert_rrefresh.
      + apply n2h_sequent_allvars.
      + now apply good_for_s2f. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Ssequent | apply IHpi1 ] | apply IHpi2 ]; auto.
  now inversion Hg' as [ | ? ? Hgi Hgl]; destruct Hgi; constructor.
- remember (flat_map (fun C => hallvars (n2h_formula r C)) (frl x A :: l)) as lv.
  remember (vfresh lv) as y.
  remember (rup (hvar y) r) as r1.
  specialize IHpi with r1.
  assert (Forall (rgood_for r1) (subs x (dvar 0) (fup 0 A) :: map (fup 0) l)) as pi'.
  { inversion_clear Hg as [ | ? ? Hgf Hgl ]; constructor.
    - simpl in Hgf; apply good_for_rup_subs with (x:= x) (y:= y) in Hgf; intuition.
      + rewrite <- (app_nil_l _) in Hgf; apply lgood_for_less in Hgf; now subst.
      + simpl in H; destruct H; intuition; subst x.
        apply vfresh_prop with lv; subst lv; in_solve.
      + apply vfresh_prop with lv; rewrite <- Heqy; subst lv; in_solve.
    - apply Forall_forall; intros B HB.
      apply in_map_iff in HB; destruct HB as [C [Heq HC]]; subst B.
      specialize_Forall Hgl with C.
      now subst r1; apply good_for_rup. }
  apply IHpi in pi'.
  apply (hprove_GEN y) in pi'.
  assert (hprove (n2h_sequent r1 (map (fup 0) l) (frl y (subs x (tvar y) (fup 0 A))))) as pi''.
  { eapply hprove_MP; [ apply hprove_FRLsequent | ].
    - intros Hin.
      apply vfresh_prop with lv; rewrite <- Heqy; subst lv.
      apply in_flat_map in Hin; destruct Hin as [C [HCin HinC]].
      apply hffreevars_hallvars in HinC.
      apply in_map_iff in HCin; destruct HCin as [D [Heq HD]]; subst C.
      rewrite Heqr1, n2h_rup in HinC.
      apply in_flat_map; exists D; in_solve.
    - enough (n2h_sequent r1 (map (fup 0) l) (subs x (dvar 0) (fup 0 A))
            = n2h_sequent r1 (map (fup 0) l) (subs x (tvar y) (fup 0 A))) as Heq
        by now rewrite <- Heq.
      enough (n2h_formula r1 (subs x (dvar 0) (fup 0 A)) = n2h_formula r1 (subs x (tvar y) (fup 0 A))) as HeqBC.
      { remember (subs x (dvar 0) (fup 0 A)) as B.
        remember (subs x (tvar y) (fup 0 A)) as C.
        clear - HeqBC; revert B C HeqBC; induction l; simpl; intros B C HeqBC; intuition.
        apply IHl; simpl; f_equal; intuition. }
      subst r1; clear; formula_induction A; term_induction t. }
  remember (frl y (subs x (tvar y) (fup 0 A))) as B.
  remember (frl x A) as C.
  assert (hprove (n2h_formula r1 B ⟶ n2h_formula r C)) as pi'''.
  { subst B C; clear - Hg Heqr1 Heqy Heqlv; simpl.
    eapply hprove_MP; [ apply hprove_FRL | ].
    - simpl; intros Hin.
      apply in_remove in Hin; destruct Hin as [Hin Hneq]; apply Hneq.
      inversion_clear Hg as [ | ? ? Hgx _ ]; simpl in Hgx.
      apply good_for_rup with (t:= hvar y) in Hgx; rewrite <- Heqr1 in Hgx.
      rewrite n2h_subs with (lv:= x :: nil) in Hin; intuition.
      apply hffreevars_subs in Hin; simpl in Hin; intuition.
    - assert (~ In y (hallvars (n2h_formula r1 (fup 0 A)))) as HA.
      { intros Hin; rewrite Heqr1, n2h_rup in Hin.
        apply vfresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy; in_solve. }
      apply hprove_GEN.
      eapply hprove_CUT; [ apply hprove_INST with (t:=hvar x) | ]; simpl.
      + repeat constructor.
        revert HA; clear; formula_induction A.
        * refine ?[mygoal]. Existential 6 := ?mygoal.
          revert H; case_analysis; intros Hin; [ | intuition ].
          exfalso; apply HA.
          apply in_remove in Hin; destruct Hin as [Hin _]; apply hffreevars_hallvars in Hin; intuition.
      + enough (hfsubs y (hvar x) (n2h_formula r1 (subs x (tvar y) (fup 0 A))) = n2h_formula r A) as Heq
          by (rewrite Heq; apply hprove_I).
        rewrite n2h_subs with (lv:=x::nil); simpl; intuition; subst r1.
        * rewrite hbisubs; intuition.
          apply n2h_rup.
        * apply good_for_rup.
          now inversion Hg. }
  clear - Heqr1 pi'' pi'''.
  revert B C pi''' pi''; induction l; simpl; intros B C pBC pi.
  + eapply hprove_MP; eassumption.
  + apply IHl with (imp (fup 0 a) B); intuition; simpl.
    subst r1; rewrite n2h_rup.
    eapply hprove_MP; [ apply hprove_B | apply pBC ].
- assert ({rf : _ & Forall (rgood_for rf) (frl x A :: l) /\ rgood_for rf (subs x u A)
                  & hprove (n2h_sequent rf l (subs x u A)) -> hprove (n2h_sequent r l (subs x u A))})
    as [rf [Hg1 Hg2] Hp].
  { exists (rrefresh (hallvars (n2h_formula r (frl x A)))
                     (flat_map (fun C => hallvars (n2h_formula r C)) (subs x u A :: l)) r).
    - split; [ constructor; simpl | ].
      + apply (good_for_refresh _ (frl x A) _ (hallvars (n2h_formula r (frl x A)))).
        rewrite app_nil_r; now intros z Hz.
      + apply Forall_forall; intros C HC.
        apply (good_for_refresh_preserv (hallvars (n2h_formula r (frl x A)))).
        * rewrite app_nil_r; intros z Hz; apply in_or_app; right.
          apply in_flat_map; exists C; intuition.
          apply n2h_allvars; in_solve.
        * inversion_clear Hg as [ | ? ? _ Hgl ].
          now specialize_Forall Hgl with C.
      + apply good_for_refresh_preserv.
        * rewrite app_nil_r; intros z Hz; apply in_or_app; left.
          apply n2h_allvars; in_solve.
        * now inversion Hg.
    - remember (subs x u A) as B.
      apply good_for_hilbert_rrefresh.
      + apply n2h_sequent_allvars.
      + now apply good_for_s2f. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply IHpi ]; auto.
  rewrite n2h_subs with (lv:=x::nil); [ apply hprove_INST | | ]; intuition.
  + apply lgood_hgood_closed with (lv := nil) (lv' := x :: nil); intuition.
    now inversion Hg1.
  + now inversion Hg1.
- assert ({rf : _ & Forall (rgood_for rf) (exs x A :: l) /\ rgood_for rf (subs x u A)
                  & hprove (n2h_sequent rf l (exs x A)) -> hprove (n2h_sequent r l (exs x A))})
    as [rf [Hg1 Hg2] Hp].
  { exists (rrefresh (hallvars (n2h_formula r (subs x u A)))
                     (flat_map (fun C => hallvars (n2h_formula r C)) (exs x A :: l)) r).
    - split; [ constructor; simpl | ].
      + apply good_for_refresh_preserv.
        * intros z Hz; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; try in_solve.
          eapply or_introl in Hz; apply in_or_app, n2h_allvars with (r:= r) in Hz; in_solve.
        * now inversion Hg.
      + apply Forall_forall; intros C HC.
        apply (good_for_refresh_preserv (hallvars (n2h_formula r (subs x u A)))).
        * rewrite app_nil_r; intros z Hz; right; apply in_or_app; right.
          apply in_flat_map; exists C; intuition.
          apply n2h_allvars; in_solve.
        * inversion_clear Hg as [ | ? ? _ Hgl ].
          now specialize_Forall Hgl with C.
      + apply (good_for_refresh _ (subs x u A) _ (hallvars (n2h_formula r (subs x u A)))).
        rewrite app_nil_r; now intros z Hz.
    - remember (exs x A) as B.
      apply good_for_hilbert_rrefresh.
      + apply n2h_sequent_allvars.
      + now apply good_for_s2f. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply IHpi ]; auto.
  + rewrite n2h_subs with (lv:=x::nil); simpl; [ apply hprove_EINST | | ]; intuition.
    * apply lgood_hgood_closed with (lv := nil) (lv' := x :: nil); intuition.
      now inversion Hg1.
    * now inversion Hg1.
  + inversion Hg1; now constructor.
- remember (rrefresh (hallvars (n2h_formula r (exs x A)))
                     (flat_map (fun C => hallvars (n2h_formula r C)) (C :: l)) r) as r1.
  assert (Forall (rgood_for r1) (C :: l)) as HgCl1.
  { apply Forall_forall; intros D HD.
    specialize_Forall Hg with D.
    subst r1; apply good_for_refresh_preserv; intuition.
    rewrite app_nil_r; intros z Hz.
    apply in_flat_map; exists D; intuition.
    apply n2h_allvars; in_solve. }
  assert (rgood_for r1 C) as HgC1 by (now inversion HgCl1).
  assert (Forall (rgood_for r1) l) as Hgl1 by (now inversion HgCl1); clear HgCl1.
  assert (rgood_for r1 (exs x A)) as HgA1
    by (subst; apply good_for_refresh; rewrite app_nil_r; now intros z Hz).
  apply good_for_hilbert_rrefresh with (l:=hallvars (n2h_formula r (exs x A)))
                                       (ld:=flat_map (fun C => hallvars (n2h_formula r C)) (C :: l)).
  + apply n2h_sequent_allvars.
  + now apply good_for_s2f.
  + rewrite <- Heqr1.
    eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Ssequent | ] | apply IHpi1; constructor; auto ].
    apply hprove_imp_sequent.
    remember (flat_map (fun C => hallvars (n2h_formula r1 C)) (exs x A :: C :: l)) as lv.
    remember (vfresh lv) as y.
    assert (hprove (hexs x (n2h_formula r1 A) ⟶ hexs y (hfsubs x (hvar y) (n2h_formula r1 A)))) as pi'.
    { remember (n2h_formula r1 A) as B; clear - HeqB Heqy Heqlv.
      assert (~ In y (hallvars B)) as Hf
        by (intros Hin; subst B; apply vfresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy; in_solve).
      clear - Hf; eapply hprove_MP; [ apply hprove_EXS | ].
      - simpl; intros Hin; apply Hf.
        apply in_remove in Hin; destruct Hin as [Hin _].
        apply hffreevars_subs in Hin; destruct Hin as [Hin|Hin]; intuition.
        simpl in H; destruct H; intuition; subst.
        now apply hffreevars_hallvars.
      - apply hprove_GEN.
        replace (B ⟶ hexs y (hfsubs x (hvar y) B))
           with (hfsubs y (hvar x) (hfsubs x (hvar y) B) ⟶ hexs y (hfsubs x (hvar y) B))
          by now rewrite hbisubs.
        apply hprove_EINST.
        simpl; repeat constructor.
        revert Hf; formula_induction B.
        * refine ?[mygoal]. Existential 2 := ?mygoal.
          revert H; case_analysis; intros Hin; apply in_remove in Hin; intuition.
            -- exfalso; apply H2.
               now apply hffreevars_hallvars.
            -- apply H2.
               now apply hffreevars_hallvars. }
    simpl; eapply hprove_CUT; [ apply pi' | ].
    eapply hprove_MP; [ apply hprove_EXS | ].
    * intros Hin.
      apply vfresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy.
      simpl; right; apply in_or_app; right.
      apply n2h_sequent_allvars, n2h_allvars; in_solve.
    * apply hprove_GEN.
      replace (hvar y) with (n2h_term r1 (tvar y)) by reflexivity.
      rewrite <- n2h_subs with (lv:=x::nil); auto; [ | now constructor ].
      apply hprove_sequent_imp.
      remember (rup (hvar y) r1) as r2.
      assert (Forall (rgood_for r2) (fup 0 C :: subs x (dvar 0) (fup 0 A) :: map (fup 0) l)) as pi.
      { constructor; [ | constructor ]; subst r2.
        - now apply good_for_rup.
        - simpl in HgA1; apply good_for_rup_subs with (x:=x) (y:=y) in HgA1; intuition.
          + rewrite <- (app_nil_l _) in HgA1; now apply lgood_for_less in HgA1.
          + simpl in H; destruct H; intuition; subst x.
            apply vfresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy; now left.
          + apply vfresh_prop with lv; rewrite Heqlv at 2; rewrite <- Heqy; in_solve.
        - apply Forall_forall; intros E HE.
          apply in_map_iff in HE; destruct HE as [E' [Heq HE]]; subst E.
          specialize_Forall Hgl1 with E'.
          now apply good_for_rup. }
      apply IHpi2 in pi; simpl in pi.
      remember (imp (subs x (dvar 0) (fup 0 A)) (fup 0 C)) as B.
      remember (imp (subs x (tvar y) A) C) as D.
      assert (hprove (n2h_formula r2 B ⟶ n2h_formula r1 D)) as HBD.
      { subst B D r2; simpl; rewrite ? n2h_rup.
        rewrite n2h_rup_subs with (lv:=x::nil); intuition.
        enough (n2h_formula r1 (subs x (tvar y) A) = hfsubs x (hvar y) (n2h_formula r1 A))
          as Heq by (rewrite Heq; apply hprove_I).
        apply n2h_subs with (x :: nil); intuition. }
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
intros r Hc A pi; change (n2h_formula r A) with (n2h_sequent r nil A).
now apply n2h; [ | apply Forall_forall; intros; apply lgood_for_closed ].
Qed.

End N2H.

