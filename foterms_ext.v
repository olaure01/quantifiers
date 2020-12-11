(* More Properties of First-Order Terms *)

Require Import ollibs.List_more.
Require Export ollibs.dectype.

Require Export term_tactics foterms.

Set Implicit Arguments.


Section Terms.

Context { vatom : DecType } { tatom : Type }.

Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").
Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation "x ∉ t" := (~ In x (tvars t)) (at level 30).
Notation closed t := (tvars t = nil).
Notation fclosed r := (forall n, closed (r n)).

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

Section Fixed_Eigen_Type.

Variable T : Type.
Implicit Type t : @term vatom tatom T.
Arguments tvar {_} {_} {_} _.

Lemma tvars_tsubs : forall x y u t,
  x ∈ t[u//y] <-> (x ∈ u /\ y ∈ t) \/ (x ∈ t /\ x <> y).
Proof. split; term_induction t.
- e_case_analysis; auto.
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

End Fixed_Eigen_Type.


Section Two_Eigen_Types.

Variable T1 T2 : Type.
Variable r : T1 -> @term vatom tatom T2.
Implicit Type t : @term vatom tatom T1.

Notation "t ⟦ r ⟧" := (tesubs r t) (at level 8, format "t ⟦ r ⟧").
Notation "x ∈ t" := (In x (tvars t)) (at level 30).
Notation "x ∉ t" := (~ In x (tvars t)) (at level 30).
Notation closed t := (tvars t = nil).
Notation fclosed := (forall n, closed (r n)).
Notation "t [ u // x ]" := (tsubs x u t) (at level 8, format "t [ u // x ]").
Notation "t [[ L ]]" := (multi_tsubs L t) (at level 8, format "t [[ L ]]").

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
Hint Rewrite tsubs_tesubs_notecap using try (intuition; fail);
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
destruct a; rewrite IHL, tsubs_tesubs_notecap; intuition.
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

End Two_Eigen_Types.


(** * Eigen variables *)
Fixpoint teigen_max (t : @term vatom tatom nat) :=
match t with
| tvar _ _ => 0
| evar n => n
| tconstr _ l => list_max (map teigen_max l)
end.

End Terms.
