(* More about First-Order Formulas *)

Require Import ollibs.List_more ollibs.List_assoc.

Require Export foterms_ext foformulas.

Set Implicit Arguments.


(** * First-Order Formulas *)
(* parametrized by a set of binary connectives and a set of unary quantifiers *)

Section Formulas.

Context { vatom : DecType } { tatom fatom : Type }.
Context { NCon BCon QCon : Type }.

Notation term := (@term vatom tatom).
Arguments evar _ _ {T}.
Notation evar := (evar vatom tatom).
Notation formula := (@formula vatom tatom fatom NCon BCon QCon).

Notation "r ;; s" := (fecomp r s) (at level 20, format "r  ;;  s").
Notation closed t := (tvars t = nil).
Notation "⇑" := fup.
Notation "⇑[ u ] r" := (felift u r) (at level 25, format "⇑[ u ] r").

Hint Rewrite (@tesubs_evar vatom tatom) : term_db.
Hint Rewrite (@tesubs_comp vatom tatom) : term_db.
Hint Rewrite (@tsubs_tsubs_eq vatom tatom) : term_db.
Hint Rewrite (@tsubs_tsubs vatom tatom)
                        using try (intuition; fail);
                             (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@tvars_tesubs_fclosed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@tvars_tsubs_closed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@notin_tsubs vatom tatom)
                         using try easy;
                              (try (intuition; fail));
                              (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@notin_tsubs_bivar vatom tatom)
                               using try easy;
                                    (try (intuition; fail));
                                    (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@tsubs_tesubs_notecap vatom tatom) using try (intuition; fail) : term_db.
Hint Rewrite (@multi_tsubs_nil vatom tatom) : term_db.

Hint Resolve tesubs_ext : term_db.
Hint Resolve closed_notvars : term_db.
Hint Resolve fclosed_no_tecapture : term_db.


Section Fixed_Eigen_Type.

Variable T : Type.
Arguments tvar {_} {_} {T} _.
Arguments tvars {_} {_} {T} _.
Implicit Type A : formula T.

Hint Rewrite (@remove_assoc_remove vatom (formula T)) : term_db.

Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").

Lemma subs_subs_eq : forall x u v A, A[v//x][u//x] = A[tsubs x u v//x].
Proof. formula_induction A. Qed.
Hint Rewrite subs_subs_eq : term_db.

(** * Variables *)

(** ** Free variables in [formula] *)
Fixpoint freevars A :=
match A with
| fvar _ l => flat_map tvars l
| fnul _ _ => nil
| fbin _ B C => freevars B ++ freevars C
| fqtf _ x B => remove eq_dt_dec x (freevars B)
end.
Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "x ∉ A" := (~ In x (freevars A)) (at level 30).

Lemma freevars_qtf : forall qcon x y, y <> x -> forall A,
  x ∈ A -> x ∈ (fqtf qcon y A).
Proof. intros; apply in_in_remove; intuition. Qed.

Lemma nfree_subs : forall x u A, x ∉ A -> A[u//x] = A.
Proof. formula_induction A.
- rnow apply notin_tsubs then apply H.
- rnow apply H.
- rcauto; rnow rewrite IHA.
  apply H, in_in_remove; intuition.
Qed.
Hint Rewrite nfree_subs using intuition; fail : term_db.

Lemma subs_subs_closed : forall x u y v, x <> y -> closed u -> closed v ->
  forall A, A[u//x][v//y] = A[v//y][tsubs y v u//x].
Proof. formula_induction A. Qed.
Hint Rewrite subs_subs_closed using intuition; fail : term_db.

Lemma freevars_subs_closed : forall x u, closed u -> forall A,
  freevars A[u//x] = remove eq_dt_dec x (freevars A).
Proof. formula_induction A; rewrite ? remove_app; try now f_equal.
- now f_equal; apply tvars_tsubs_closed.
- symmetry; apply remove_remove_eq.
- now rewrite remove_remove_comm by (now intros Heq'; apply Heq); f_equal.
Qed.
Hint Rewrite freevars_subs_closed using intuition; fail : term_db.

Lemma freevars_subs : forall x y u A,
  x ∈ A[u//y] -> (In x (tvars u) /\ y ∈ A) \/ (x ∈ A /\ x <> y).
Proof. formula_induction A; try in_solve.
- revert H; induction l; simpl; intros Hin.
  + inversion Hin.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    * apply tvars_tsubs in Hin; in_solve.
    * apply IHl in Hin; in_solve.
- revert H; case_analysis; intros H.
  + right; intuition.
    apply in_remove in H; intuition.
  + assert (Hin := proj1 (in_remove _ _ _ _ H)).
    apply IHA in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition;
      apply in_in_remove; intuition.
    subst; revert H; apply remove_In.
Qed.

(** ** No capture of [y] when susbtituted for [x] in [A] *)
Fixpoint no_capture_at x y A :=
match A with
| fvar _ _ => True
| fnul _ _ => True
| fbin _ B C => no_capture_at x y B /\ no_capture_at x y C
| fqtf qcon z B => x ∈ (fqtf qcon z B) -> no_capture_at x y B /\ y <> z
end.
Notation "y #[ x ] A" := (no_capture_at x y A) (at level 30, format "y  #[ x ]  A").

Lemma no_capture_subs_freevars : forall A x y u,
  x #[y] A -> y ∈ A -> In x (tvars u) -> x ∈ A[u//y].
Proof. formula_induction A; try in_solve.
- revert H0 H1; clear; induction l; intros Hin1 Hin2; simpl; intuition.
  simpl in Hin1.
  apply in_or_app; apply in_app_or in Hin1; destruct Hin1 as [Hin1|Hin1]; [left|right]; rcauto.
  apply tvars_tsubs; intuition.
- exfalso; now apply remove_In in H0.
- apply in_in_remove; intuition.
  apply in_remove in H0; destruct H0 as [Hin Hneq].
  apply IHA; intuition.
Qed.

Lemma no_capture_subs : forall x y z t A, closed t ->
  y #[x] A -> y #[x] A[t//z].
Proof. formula_induction A; revert H1; case_analysis; try (intuition; fail); intros Hin.
apply (remove_incl eq_dt_dec) with (l2:= freevars A) in Hin; intuition.
intros z' Hz'; apply freevars_subs in Hz'; intuition.
now exfalso; revert H3; apply closed_notvars. (* TODO automatize? *)
Qed.

Lemma subs_subs : forall x u y v, x <> y -> closed v -> forall A,
  Forall (fun y => y #[x] A) (tvars u) -> A[u//x][v//y] = A[v//y][tsubs y v u//x].
Proof. induction A; simpl; intros Hnc; f_equal.
- rnow rewrite 2 map_map; apply map_ext; rcauto.
- apply IHA1; eapply Forall_impl; [ | eassumption ]; simpl; intuition.
- apply IHA2; eapply Forall_impl; [ | eassumption ]; simpl; intuition.
- repeat case_analysis; intuition.
  + destruct (in_dec eq_dt_dec y (tvars u));
     [ destruct (in_dec eq_dt_dec x (freevars A)) | ]; rcauto.
    exfalso.
    specialize_Forall Hnc with y; apply Hnc; intuition.
    now apply in_in_remove.
  + destruct (in_dec eq_dt_dec x (freevars A)).
    * apply IHA.
      apply Forall_forall; intros z Hinz.
      specialize_Forall Hnc with z; apply Hnc.
      apply in_in_remove; intuition.
    * rewrite 2 (nfree_subs x); [ reflexivity | | assumption ].
      intros Hin; apply n.
      rewrite freevars_subs_closed in Hin; [ | assumption ].
      now apply in_remove in Hin.
Qed.
Hint Rewrite subs_subs using intuition; fail : term_db.
(* [subs_subs_closed] is a corollary of [subs_subs]:
     Proof.
       intros x u y v Hneq Hcu Hcv A.
       apply subs_subs; intuition; rewrite Hcu; constructor.
     Qed.
   but the direct proof above is much simpler *)


(** ** All variables in [formula] *)
(* occurring (free or bound or for quantification) in a formula *)
Fixpoint fvars A :=
match A with
| fvar _ l => flat_map tvars l
| fnul _ _ => nil
| fbin _ B C => fvars B ++ fvars C
| fqtf _ x B => x :: fvars B
end.

Lemma freevars_fvars : forall A, incl (freevars A) (fvars A).
Proof. formula_induction A.
eapply incl_tran; [ apply remove_incl, IHA | ].
intros y Hin; apply in_remove in Hin; intuition.
Qed.
Hint Resolve freevars_fvars : term_db.

Lemma notin_subs_bivar : forall x y A, ~ In x (fvars A) -> A[tvar x//y][tvar y//x] = A.
Proof. formula_induction A.
- apply notin_tsubs_bivar.
  intros Hin; apply H; simpl; intuition.
- apply H; simpl; intuition.
- now apply nfree_subs; intros Hin; apply H; right; apply freevars_fvars. (* TODO automatize? *)
Qed.


(** * Iterated substitution *)

Definition multi_subs L A := fold_left (fun F '(x,u) => F[u//x]) L A.
Notation "A [[ L ]]" := (multi_subs L A) (at level 8, format "A [[ L ]]").
Notation "L ∖ x" := (remove_assoc x L) (at level 18).

Lemma multi_subs_nil : multi_subs nil = id.
Proof. reflexivity. Qed.
Hint Rewrite multi_subs_nil : term_db.

Lemma multi_subs_fvar : forall L X l, (fvar X l)[[L]] = fvar X (map (multi_tsubs L) l).
Proof. induction L; intros X l; simpl.
- rcauto; now rewrite map_id.
- now destruct a; rewrite IHL, map_map.
Qed.
Hint Rewrite multi_subs_fvar : term_db.

Lemma multi_subs_fbin : forall bcon L A B,
 (fbin bcon A B)[[L]] = fbin bcon A[[L]] B[[L]].
Proof. now induction L; intros A B; simpl; [ | destruct a; rewrite IHL ]. Qed.
Hint Rewrite multi_subs_fbin : term_db.

Lemma multi_subs_fqtf : forall qcon L x A,
  (fqtf qcon x A)[[L]] = fqtf qcon x A[[remove_assoc x L]].
Proof.
induction L; intros x A; simpl; [ reflexivity | destruct a; simpl ].
case_analysis; rewrite IHL; f_equal.
Qed.
Hint Rewrite multi_subs_fqtf : term_db.

Lemma closed_multi_subs : forall L A, freevars A = nil -> A[[L]] = A.
Proof.
induction L; intros A Hc; [ reflexivity | destruct a; simpl ].
(rnow rewrite nfree_subs); rewrite Hc in H; inversion H.
Qed.
Hint Rewrite closed_multi_subs using intuition; fail : term_db.

Lemma multi_subs_closed : forall L A,
  Forall (fun z => closed z) (map snd L) -> incl (freevars A) (map fst L) ->
  freevars A[[L]] = nil.
Proof.
induction L; simpl; intros A Hc Hf.
- now apply incl_l_nil in Hf; subst.
- destruct a; simpl; simpl in Hc, Hf; inversion_clear Hc as [ | ? ? Hc2 HcF].
  apply IHL; intuition.
  intros z Hinz.
  rewrite freevars_subs_closed in Hinz by assumption.
  apply in_remove in Hinz; destruct Hinz as [Hinz Hneq].
  apply Hf in Hinz; inversion Hinz; [ exfalso | ]; intuition.
Qed.

Lemma multi_subs_freevars : forall L A,
  Forall (fun z => closed z) (map snd L) ->
  incl (freevars A[[L]]) (freevars A).
Proof.
induction L; intros A Hc x Hin; [ assumption | destruct a; simpl in Hc, Hin ].
inversion_clear Hc as [ | ? ? Hct HcF ].
apply IHL in Hin; trivial.
apply freevars_subs in Hin; destruct Hin as [ [Hin _] | ]; intuition.
exfalso; rewrite Hct in Hin; inversion Hin.
Qed.

Lemma multi_subs_subs : forall L x u,
  Forall (fun z => closed z) (map snd L) ->
  forall A, Forall (fun y => y #[x] A) (tvars u) ->
  A[u//x][[L]] = A[[L∖x]][multi_tsubs L u//x].
Proof.
induction L; simpl; intros x u Hc A Hb; [ reflexivity | destruct a; simpl; simpl in Hc ].
inversion_clear Hc as [ | ? ? Hct HcF ].
case_analysis; rewrite <- IHL; intuition; f_equal; rcauto.
- apply incl_Forall with (tvars u); intuition.
  now intros x Hin; apply in_remove in Hin.
- apply incl_Forall with (tvars u).
  + now intros y Hin; apply in_remove in Hin.
  + apply Forall_impl with (fun y => y #[x] A); trivial.
    intros a; now apply no_capture_subs.
Qed.
Hint Rewrite multi_subs_subs using intuition; fail : term_db.

Lemma multi_subs_remove : forall L A x,
  Forall (fun z => closed z) (map snd L) -> x ∉ A -> A[[L∖x]] = A[[L]].
Proof.
induction L; simpl; intros A x Hc Hin; [ reflexivity | destruct a; simpl; simpl in Hc ].
inversion_clear Hc as [ | ? ? Hct HcF ].
case_analysis; rcauto.
apply IHL; try assumption.
intros Hin2; apply Hin.
apply freevars_subs in Hin2.
destruct Hin2 as [ [Hin2 _] | [Hin2 _] ]; trivial.
exfalso; rewrite Hct in Hin2; inversion Hin2.
Qed.
Hint Rewrite multi_subs_remove using intuition; fail : term_db.

Lemma multi_subs_extend : forall L A,
  Forall (fun z => closed z) (map snd L) -> incl (freevars A) (map fst L) ->
  forall L', A[[L]] = A[[L ++ L']].
Proof.
intros L A Hcl Hsub L'.
unfold multi_subs at 2; rewrite fold_left_app.
rewrite closed_multi_subs
  with (A:= fold_left (fun F '(x,u) => F[u//x]) L A); trivial.
now apply multi_subs_closed.
Qed.

End Fixed_Eigen_Type.


Section Two_Eigen_Types.

Variable T1 T2 : Type.
Variable r : T1 -> term T2.
Implicit Type A : @formula T1.

Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").
Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "x ∉ A" := (~ In x (freevars A)) (at level 30).
Notation fclosed := (forall n, closed (r n)).
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "A [[ L ]]" := (multi_subs L A) (at level 8, format "A [[ L ]]").
Notation "y #[ x ] A" := (no_capture_at x y A) (at level 30, format "y  #[ x ]  A").

(** * Additional results with variable eigen type *)

Lemma freevars_esubs_fclosed : fclosed -> forall A, freevars A⟦r⟧ = freevars A.
Proof. formula_induction A.
- now rewrite IHA1, IHA2.
- now rewrite IHA.
Qed.
Hint Rewrite freevars_esubs_fclosed using intuition; fail : term_db.

Lemma no_capture_esubs : fclosed -> forall x y A, y #[x] A -> y #[x] A⟦r⟧.
Proof. formula_induction A. Qed.

Lemma fvars_esubs : forall A,
  incl (fvars A ++ freevars A⟦r⟧) (fvars A⟦r⟧).
Proof. formula_induction A; simpl; intros z Hin; try in_solve.
- revert Hin; induction l; simpl; intros Hin; try in_solve.
  apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition.
  now eapply tvars_tesubs.
- inversion_clear Hin; subst; intuition.
  apply in_cons, IHA.
  apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right]; auto.
  now apply in_remove in H.
Qed.

(** * No capture generated by [r] in [A] under virtual binders for [lv] *)
Fixpoint no_ecapture_at lv A :=
match A with
| fvar X l => fold_right (fun t P => and (no_tecapture_at r lv t) P) True l
| fnul _ _ => True
| fbin _ B C => no_ecapture_at lv B /\ no_ecapture_at lv C
| fqtf _ z B => no_ecapture_at (z :: lv) B
end.
Notation "#[[ lv ]] A" := (no_ecapture_at lv A) (at level 30, format "#[[ lv ]]  A").

Lemma no_ecapture_less : forall A lv1 lv2, incl lv1 lv2 ->
  #[[lv2]] A -> #[[lv1]] A.
Proof. formula_induction A.
- apply Forall_fold_right in H0; apply Forall_fold_right.
  eapply Forall_impl; [ intros t; apply no_tecapture_less | ]; eassumption.
- eapply IHA1; eassumption.
- eapply IHA2; eassumption.
- eapply IHA; [ | eassumption ]; in_solve.
Qed.

Lemma fclosed_no_ecapture : fclosed -> forall A lv, #[[lv]] A.
Proof. formula_induction A. Qed.
Hint Resolve fclosed_no_ecapture : term_db.

Lemma no_ecapture_subs_nfree : forall x y u A,
  closed u -> #[[y::nil]] A[u//x] ->
  In y (tvars (tesubs r u)) -> x ∉ A.
Proof. formula_induction A; try in_solve; intros Hinx.
- apply Forall_fold_right in H0.
  rewrite <- flat_map_concat_map in Hinx.
  apply in_flat_map in Hinx; destruct Hinx as [ z [Hinzl Hinz] ].
  apply in_map with (f:= tsubs x u) in Hinzl.
  specialize_Forall H0 with (tsubs x u z).
  apply no_tecapture_subs_notin in H0; intuition.
- apply in_remove in Hinx; destruct Hinx as [Hin Hneq].
  revert H0; case_analysis; intros Hg; intuition.
  apply no_ecapture_less with (lv1:= y::nil) in Hg; [ intuition | in_solve ].
Qed.

Fixpoint not_egenerated x A :=
match A with
| fvar X l => fold_right (fun t P => and (no_tecapture_at r (x::nil) t) P) True l
| fnul _ _ => True
| fbin _ B C => not_egenerated x B /\ not_egenerated x C
| fqtf _ z B => x <> z -> not_egenerated x B
end.

Lemma no_ecapture_not_egenerated : forall x A, #[[x::nil]] A -> not_egenerated x A.
Proof. formula_induction A.
apply no_ecapture_less with (lv1:= x::nil) in H; [ intuition | in_solve ].
Qed.
Hint Resolve no_ecapture_not_egenerated : term_db.

Lemma esubs_freevars : forall x A, not_egenerated x A -> x ∈ A⟦r⟧ -> x ∈ A.
Proof. formula_induction A; try in_solve.
- rewrite flat_map_map in H0; apply in_flat_map in H0; destruct H0 as [ t [Htin Hint] ].
  apply Forall_fold_right in H; specialize_Forall H with t.
  apply tesubs_tvars in Hint; intuition.
  rewrite <- flat_map_concat_map; apply in_flat_map; exists t; intuition.
- apply in_remove in H0; destruct H0 as [Hin Hneq].
  apply in_in_remove; intuition.
Qed.

Lemma subs_esubs_notegen : forall x u A, not_egenerated x A ->
  A[u//x]⟦r⟧ = A⟦r⟧[tesubs r u//x].
Proof. formula_induction A; simpl in H; rcauto. Qed.
Hint Rewrite subs_esubs_notegen using try (intuition; fail);
                             (try apply no_ecapture_not_egenerated); try (intuition; fail);
                             (try apply fclosed_no_ecapture); intuition; fail : term_db.

Lemma multi_subs_esubs : forall L A, fclosed ->
  A[[L]]⟦r⟧ = A⟦r⟧[[map (fun '(x, u) => (x, tesubs r u)) L]].
Proof. induction L; simpl; intros A Hc; [ reflexivity | ].
destruct a; rewrite IHL, subs_esubs_notegen; intuition.
Qed.
Hint Rewrite multi_subs_esubs : term_db.

Lemma no_ecapture_esubs_subs_closed : forall u x A,
  closed u -> #[[nil]] A[u//x] -> not_egenerated x A ->
  Forall (fun z => z #[x] A⟦r⟧) (tvars (tesubs r u)).
Proof. formula_induction A.
- now apply Forall_forall.
- now apply Forall_forall.
- apply Forall_and; intuition.
- revert H0; case_analysis; intros H0.
  + apply Forall_forall; intros z Hz Hin.
    exfalso; now apply in_remove in Hin.
  + assert (Hx0 := H0).
    apply no_ecapture_less with (lv1:= nil) in H0; [ | in_solve ].
    apply IHA in H0; intuition.
    apply Forall_forall; intros z Hz Hin.
    specialize_Forall H0 with z; split; [ assumption | ].
    intros Heq2; subst.
    apply in_remove in Hin; destruct Hin as [Hin _].
    apply esubs_freevars in Hin; intuition.
    apply no_ecapture_subs_nfree in Hx0; intuition.
Qed.

End Two_Eigen_Types.

Hint Rewrite freevars_esubs_fclosed using intuition; fail : term_db.

Fixpoint eigen_max (A : formula nat) :=
match A with
| fvar _ l => list_max (map teigen_max l)
| fnul _ _ => 0
| fbin _ B C => max (eigen_max B) (eigen_max C)
| fqtf _ _ B => eigen_max B
end.

Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").
Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").

Lemma freevars_fup : forall (A : formula nat), freevars A↑ = freevars A.
Proof. rcauto. Qed.
Hint Rewrite freevars_fup : term_db.

End Formulas.
