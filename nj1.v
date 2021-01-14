(* Natural Deduction for First-Order Intuitionistic Logic *)

From Coq Require Import Wf_nat Lia.
From OLlibs Require Import List_more.

Require Export foformulas_ext.

Set Implicit Arguments.


(** * Proofs *)

Section Proofs.

Context { vatom : DecType } { tatom fatom : Type }.

Arguments tvar {_} {_} {T} _.

Notation term := (@term vatom tatom nat).
Notation closed t := (tvars t = nil).
Notation fclosed r := (forall n, closed (r n)).
Notation "↑ r" := (felift (evar 0) r) (at level 25, format "↑ r").
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "⇑" := fup.
Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "l ⇈" := (map (fun F => F↑) l) (at level 8, format "l ⇈").

Notation formula := (@formula vatom tatom fatom Nocon Nocon Icon Qcon nat).

Hint Rewrite (@fsize_esubs vatom tatom fatom Nocon Nocon Icon Qcon) : term_db.
Hint Rewrite (@fsize_subs vatom tatom fatom Nocon Nocon Icon Qcon nat) : term_db.
Hint Rewrite (@tvars_tesubs_fclosed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@freevars_esubs_fclosed vatom tatom fatom Nocon Nocon Icon Qcon nat)
                 using intuition; fail : term_db.
Hint Rewrite (@subs_esubs_notegen vatom tatom fatom Nocon Nocon Icon Qcon nat)
                         using try (intuition; fail);
                             (try apply no_ecapture_not_egenerated); try (intuition; fail);
                             (try apply fclosed_no_ecapture); intuition; fail : term_db.
Hint Rewrite <- (@felift_esubs vatom tatom fatom Nocon Nocon Icon Qcon) : term_db.
Hint Rewrite (@esubs_fup vatom tatom fatom Nocon Nocon Icon Qcon) : term_db.

Hint Resolve fclosed_felift : term_db.
Hint Resolve fclosed_fesubs : term_db.


(** Proofs *)
Inductive prove : list formula -> formula -> Type :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi l A B : prove (A :: l) B -> prove l (imp A B)
| impe l B : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli x l A : prove l⇈ A↑[evar 0//x] -> prove l (frl x A)
| frle x l A : forall u, closed u -> prove l (frl x A) -> prove l (subs x u A)
| exsi x l A : forall u, closed u -> prove l (subs x u A) -> prove l (exs x A)
| exse l C : forall x A, prove l (exs x A) -> prove (A↑[evar 0//x] :: l⇈) C↑ -> prove l C.
Hint Constructors prove : term_db.
Global Arguments impe { l B }.
Global Arguments exse { l C }.

Lemma ax_hd {l A} : prove (A :: l) A.
Proof (ax nil l A).


(** Normal Forms *)
Inductive nprove : list formula -> formula -> Type := (* neutral terms *)
| nax : forall l1 l2 A, nprove (l1 ++ A :: l2) A
| nimpe l B : forall A, nprove l (imp A B) -> rprove l A -> nprove l B
| nfrle x l A : forall u, closed u -> nprove l (frl x A) -> nprove l (subs x u A)
with rprove : list formula -> formula -> Type := (* normal forms *)
| rninj l A : nprove l A -> rprove l A
| rimpi l A B : rprove (A :: l) B -> rprove l (imp A B)
| rfrli x l A : rprove l⇈ A↑[evar 0//x] -> rprove l (frl x A)
| rexsi x l A : forall u, closed u -> rprove l (subs x u A) -> rprove l (exs x A)
| rexse l C : forall x A, nprove l (exs x A) -> rprove (A↑[evar 0//x] :: l⇈) C↑ -> rprove l C.
Hint Constructors nprove rprove : term_db.
Global Arguments rfrli { x l A }.
Global Arguments rexsi { x l A }.
Global Arguments nimpe { l B }.
Global Arguments rexse { l C }.

Scheme nrprove_rect := Induction for nprove Sort Type
  with rnprove_rect := Induction for rprove Sort Type.
Combined Scheme rnprove_mutrect from nrprove_rect, rnprove_rect.

Lemma nax_hd {l A} : nprove (A :: l) A.
Proof (nax nil l A).
Hint Resolve nax_hd : term_db.

(* automatic tactic for application of the [nax] constructor *)
Ltac run_nax :=
  match goal with
  | |- nprove (?l1 ++ ?B :: ?l2) ?A => (try now apply nax);
         rewrite <- (app_nil_l l2); rewrite app_comm_cons, app_assoc; run_nax
  | |- nprove (?l1 ++ ?l2 ++ ?l3) ?A => rewrite app_assoc; run_nax
  end.
Ltac auto_nax := rewrite <- (app_nil_l _); run_nax.

(* Apply all (reversible) introduction rules *)
Ltac rev_intros := intros; repeat (repeat apply rimpi; repeat (apply rfrli; simpl)); apply rninj.

Fixpoint nsize {l A} (pi : nprove l A) : nat :=
match pi with
| nax _ _ _  => 1
| nimpe _ pi1 pi2 => S (nsize pi1 + rsize pi2)
| nfrle _ _ pi0 => S (nsize pi0)
end
with rsize {l A} (pi : rprove l A) : nat :=
match pi with
| rninj pi0 => S (nsize pi0)
| rimpi pi0 => S (rsize pi0)
| rfrli pi0 => S (rsize pi0)
| rexsi _ _ pi0 => S (rsize pi0)
| rexse _ _ pi1 pi2 => S (nsize pi1 + rsize pi2)
end.

Theorem denormalization :
   (forall l A, nprove l A -> prove l A)
 * (forall l A, rprove l A -> prove l A).
Proof. now apply rnprove_mutrect; intros; try (econstructor; eassumption). Qed.


(** * Normalization *)

(** apply [r] in normal form *)
Theorem rnpesubs r (Hc : fclosed r) {l A} :
   (nprove l A -> nprove (map (esubs r) l) A⟦r⟧)
 * (rprove l A -> rprove (map (esubs r) l) A⟦r⟧).
Proof.
revert l A.
enough ((forall l A, nprove l A -> forall r, fclosed r -> nprove (map (esubs r) l) A⟦r⟧)
      * (forall l A, rprove l A -> forall r, fclosed r -> rprove (map (esubs r) l) A⟦r⟧))
  as He by (split; intros; apply He; assumption).
clear r Hc; apply rnprove_mutrect; intros; (try simpl in X);
  (try assert (IH1 := X r H)); (try assert (IH2 := X0 r H));
  (try (econstructor; (eassumption + intuition); fail)).
- rewrite map_app; apply nax.
- rcauto; rnow apply nfrle.
- specialize X with (↑r0).
  revert X; rcauto.
  rewrite map_map, <- (map_ext _ _ (felift_esubs (evar 0) _)), <- map_map in X; intuition.
- specialize X with r0.
  rnow apply (rexsi (tesubs r0 u)).
- specialize X0 with (↑r0); simpl in X0.
  rewrite map_map, <- (map_ext _ _ (felift_esubs (evar 0) _)), <- map_map in X0.
  rnow eapply rexse.
Qed.

Lemma rpsubsz_r {l A x u} : closed u ->
  rprove l⇈ A↑[evar 0//x] -> rprove l (subs x u A).
Proof.
intros Hc pi.
apply (rnpesubs (u⇓)) in pi; [ | intuition ].
rnow simpl in pi then simpl in pi.
now rewrite map_map, (map_ext _ _ (esubs_fup _)), map_id in pi.
Qed.

Lemma rpsubsz_l {l A x u C} : closed u ->
  rprove (A↑[evar 0//x] :: l⇈) C↑ -> rprove (subs x u A :: l) C.
Proof.
intros Hc pi.
apply (rnpesubs (u⇓)) in pi; [ | intuition ].
rnow simpl in pi then simpl in pi.
now rewrite map_map, (map_ext _ _ (esubs_fup _)), map_id in pi.
Qed.

Lemma rweakening :
   (forall l A, nprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> nprove (l1 ++ l0 ++ l2) A)
 * (forall l A, rprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> rprove (l1 ++ l0 ++ l2) A).
Proof.
apply rnprove_mutrect; intros; subst;
  try (econstructor; rewrite_all map_app; rewrite ? app_comm_cons; intuition; intuition; fail).
destruct (dichot_elt_app_inf _ _ _ _ _ H) as [ [? [? ?]] | [? [? ?]] ]; subst;
  rewrite ? (app_assoc _ _ (A::_)), <- ? (app_assoc _ (A::_)), <- ? app_comm_cons;
  intuition.
Qed.

Lemma imp_reduction : forall A B l, rprove l (imp A B) ->
(forall D l B, fsize D = fsize A -> rprove (D :: l) B -> rprove l D -> rprove l B) ->
  rprove l A -> rprove l B.
Proof.
intros A B l pi.
remember (imp A B) as C; revert A B HeqC; induction pi;
  intros A1 B1 HeqC; inversion HeqC; subst; intros Hsub pi2.
- apply rninj; eapply nimpe; eassumption.
- now eapply Hsub.
- eapply rexse; [ eassumption | ].
  eapply (IHpi (A1↑) (B1↑)); [ reflexivity | | ].
  + clear - Hsub; intros D l B Hs pi1 pi2.
    rnow eapply (Hsub D).
  + rewrite <- (app_nil_l l⇈), app_comm_cons, <- (app_nil_l _).
    eapply rweakening; [ | reflexivity ].
    now apply rnpesubs.
Qed.

Lemma frl_reduction : forall A x l, rprove l (frl x A) ->
  forall u, closed u -> rprove l (subs x u A).
Proof.
intros A x l pi.
remember (frl x A) as C; revert A x HeqC; induction pi;
  intros A1 x1 HeqC; inversion HeqC; subst; intros u Hc.
- apply rninj; now eapply nfrle.
- now apply rpsubsz_r.
- apply (rexse x A); trivial.
  rnow simpl in IHpi then rnow (apply IHpi).
Qed.

Lemma exs_reduction : forall A x l, rprove l (exs x A) ->
(forall D l B, fsize D = fsize A -> rprove (D :: l) B -> rprove l D -> rprove l B) ->
  forall C, rprove (A↑[evar 0//x] :: l⇈) C↑ -> rprove l C.
Proof.
intros A x l pi.
remember (exs x A) as A'; revert A x HeqA'; induction pi;
  intros A' x1 HeqA'; inversion HeqA'; subst; intros Hsub C pi2.
- eapply rexse; eassumption.
- eapply rpsubsz_l in pi2; [ | eassumption ].
  rnow apply (Hsub (A'[u//x1])).
- rnow simpl in IHpi.
  eapply rexse; [ eassumption | ].
  eapply IHpi; [ reflexivity | | ].
  + clear - Hsub; intros D l B Hs pi1 pi2.
    rnow eapply (Hsub D).
  + simpl; rewrite <- (app_nil_l (subs x _ _ :: _)),
                   app_comm_cons, <- (app_nil_l (map (esubs ⇑) _)), app_comm_cons.
    eapply rweakening; [ | reflexivity ].
    apply (rnpesubs (↑⇑)) in pi2; intuition.
    rnow simpl in pi2 then simpl in pi2.
    now rewrite map_map, <- (map_ext _ _ (felift_esubs (evar 0) _)), <- map_map in pi2.
Qed.

Lemma substitution : forall n m A, fsize A = n ->
   (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> fsize A < fsize B -> rprove (l1 ++ l2) A -> nprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : rprove (l1 ++ A :: l2) B),
      rsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B).
Proof.
apply (lt_wf_double_rect (fun n m =>
 forall A, fsize A = n ->
   (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> fsize A < fsize B -> rprove (l1 ++ l2) A -> nprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : rprove (l1 ++ A :: l2) B),
      rsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B))); simpl;
  intros n m IHn IHm A HA; (split; [ split | ] ); subst;
  intros B l1 l2 pi2 Hpi; [ intros HF | | ]; intros pi1;
  remember (l1 ++ A :: l2) as ll; destruct pi2; subst; simpl in Hpi.
(* first statement *)
- destruct (dichot_elt_app_inf _ _ _ _ _ Heqll)
    as [ (l' & Heq0 & Heq) | (l' & Heq0 & Heq) ]; subst.
  + rewrite <- app_assoc; apply nax.
  + destruct l'; inversion Heq; subst; [ lia | auto_nax ].
- assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  eapply nimpe; eapply (IHm (S (nsize pi2 + rsize r))); simpl; eauto; lia.
- apply nfrle; auto.
  rnow eapply (IHm _ Hpi).
(* second statement *)
- enough (forall l l1 l2, l0 ++ A0 :: l3 = l1 ++ A :: l2 ->
      rprove (l ++ l1 ++ l2) A -> rprove (l ++ l1 ++ l2) A0)
    as HI by (eapply (HI nil); eassumption); clear.
  induction l0; intros l l1 l2 Heq pi; destruct l1; inversion Heq; subst; auto.
  + rewrite <- app_comm_cons; apply rninj, nax.
  + rewrite 2 app_assoc; apply rninj, nax.
  + rewrite <- app_comm_cons, <- (app_nil_l l1), <- app_assoc, app_comm_cons, app_assoc.
    apply IHl0; auto.
    rewrite <- ? app_assoc, <- app_comm_cons; auto.
- assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  assert ({fsize (imp A0 B) <= fsize A} + {fsize A < fsize (imp A0 B)}) as [ Ho | Ho ]
    by (case (CompareSpec2Type (Nat.compare_spec (fsize (imp A0 B)) (fsize A))); intros Ho;
          [ left | left | right ]; lia); simpl in Ho.
  + eapply IHm in IH1; eapply IHm in IH2; auto.
    eapply imp_reduction; eauto.
    intros D l' B' Heq pi1' pi2'.
    rewrite <- (app_nil_l _) in pi1'.
    refine (snd (IHn (fsize D) (S (rsize pi1')) _ _ _) _ _ _ pi1' _ pi2'); auto; lia.
  + apply rninj; eapply nimpe; eapply IHm; eauto.
- assert (nsize pi2 < S (nsize pi2)) as IH1 by lia.
  eapply IHm in IH1; auto.
  eapply frl_reduction; auto.
(* third statement *)
- refine (snd (fst (IHm _ _ _ _)) _ _ _ n _ _); auto; lia.
- revert pi2 Hpi; rewrite app_comm_cons; intros pi2 Hpi.
  apply rimpi.
  refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _); auto; try lia.
  rewrite <- app_comm_cons, <- (app_nil_l (l1 ++ l2)), app_comm_cons, <- (app_nil_l _).
  eapply rweakening; eauto.
- apply rfrli; rewrite map_app.
  apply (rnpesubs ⇑) in pi1; intuition.
  revert pi1 pi2 Hpi; rewrite ? map_app; simpl; intros pi1 pi2 Hpi.
  rnow (refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _); auto).
- eapply rexsi; eauto.
  refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _); auto; lia.
- rewrite <- (app_nil_l _) in pi1.
  assert (pi1' := snd rweakening _ _ (snd (rnpesubs ⇑ fclosed_fup) pi1)
                  (A0↑[evar 0//x] :: nil) nil _ eq_refl) ; simpl in pi1'.
  rewrite map_app in pi1' ; rewrite app_comm_cons in pi1'.
  revert pi2 pi1' Hpi; rewrite ? map_app; simpl; rewrite app_comm_cons;
    intros pi2 pi1' Hpi.
  assert (fsize (A↑) = fsize A) as Hup by rcauto.
  eapply (snd (IHm _ Hpi _ Hup) _ _ _ pi2) in pi1'; [ | lia].
  assert ({fsize (exs x A0) <= fsize A} + {fsize A < fsize (exs x A0)}) as [ Ho | Ho ]
    by (case (CompareSpec2Type (Nat.compare_spec (fsize (exs x A0)) (fsize A))); intros Ho;
          [ left | left | right ]; lia); simpl in Ho.
  + eapply (snd (fst (IHm _ Hpi _ eq_refl)) _ _ _ n) in pi1; [ | lia ].
    simpl in pi1' ; rewrite <- map_app in pi1'.
    eapply exs_reduction; eauto.
    intros D l' B' Heq pi1'' pi2''.
    rewrite <- (app_nil_l _) in pi1''.
    refine (snd (IHn (fsize D) (S (rsize pi1'')) _ _ _) _ _ _ pi1'' _ pi2''); lia.
  + eapply rexse.
    * refine (fst (fst (IHm _ _ _ _ )) _ _ _ n _ _ _); auto; lia.
    * rewrite map_app; auto.
Qed.

Lemma smp_substitution : forall l A B, rprove l A -> rprove (A :: l) B -> rprove l B.
Proof.
intros l A B pi1 pi2.
rewrite <- (app_nil_l (A :: l)) in pi2; rewrite <- (app_nil_l l).
refine (snd (substitution (S (rsize pi2)) _ _ ) _ _ _ pi2 _ _); intuition.
Qed.

Theorem normalization : forall l A, prove l A -> rprove l A.
Proof.
intros l A pi; induction pi;
   try (econstructor; (idtac + econstructor); eassumption).
- apply (imp_reduction IHpi1); [ | assumption ].
  intros; eapply smp_substitution; eassumption.
- now apply frl_reduction.
- apply (exs_reduction IHpi1); [ | assumption ].
  intros; eapply smp_substitution; eassumption.
Qed.


(** * Sub-Formula Property *)

(** Sub-formula Relation *)
Inductive subform : formula -> formula -> Prop :=
| sub_id : forall A, subform A A
| sub_imp_l : forall A B C, subform A B -> subform A (imp B C)
| sub_imp_r : forall A B C, subform A B -> subform A (imp C B)
| sub_frl : forall A x u B, subform A (subs x u B) -> subform A (frl x B)
| sub_exs : forall A x u B, subform A (subs x u B) -> subform A (exs x B)
| sub_frl_n : forall A x B, subform A B↑[evar 0//x] -> subform A (frl x B)
| sub_ex_n : forall A x B, subform A B↑[evar 0//x] -> subform A (exs x B)
| sub_fup : forall A B, subform A B↑ -> subform A B.

Lemma subform_trans : forall A B C, subform A B -> subform B C -> subform A C.
Proof.
now intros A B C Hl Hr; revert A Hl; induction Hr; intros A' Hl; try (econstructor; apply IHHr).
Qed.

Lemma subform_fupz : forall A B, subform A B -> subform A↑ B↑.
Proof.
intros A B Hs; induction Hs; try (now econstructor; eauto).
- rcauto; econstructor; eauto.
- rcauto; econstructor; eauto.
- eapply subform_trans; [ apply IHHs | ].
  apply sub_fup; simpl.
  apply (sub_frl _ (evar 1)).
  rcauto; apply sub_id.
- eapply subform_trans; [ apply IHHs | ].
  apply sub_fup; simpl.
  apply (sub_exs _ (evar 1)).
  rcauto; apply sub_id.
Qed.

(* restricted notion of sub-formula *)
Inductive lsubform : formula -> formula -> Prop :=
| lsub_id : forall A, lsubform A A
| lsub_imp_r : forall A B C, lsubform (imp A B) C -> lsubform B C
| lsub_frl : forall A x u B, lsubform (frl x A) B -> lsubform (subs x u A) B
| lsub_exs : forall A x u B, lsubform (exs x A) B -> lsubform (subs x u A) B.

Lemma lsubform_trans : forall A B C, lsubform A B -> lsubform B C -> lsubform A C.
Proof.
intros A B C Hl Hr ; revert C Hr ; induction Hl ; intros C' Hr; auto;
  try (econstructor; now apply IHHl).
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

(* property [P] holds for any formula in [pi] *)
Fixpoint nprove_with_prop P {l A} (pi : nprove l A) : Prop :=
match pi with
| nax l1 l2 A  => Forall P l1 /\ Forall P l2 /\ P A
| @nimpe _ B _ pi1 pi2 => P B /\ nprove_with_prop P pi1 /\ rprove_with_prop P pi2
| @nfrle x _ A u _ pi0 => P (subs x u A) /\ nprove_with_prop P pi0
end
with rprove_with_prop P {l A} (pi : rprove l A) : Prop :=
match pi with
| rninj pi0 => nprove_with_prop P pi0
| @rimpi _ A B pi0 => P (imp A B) /\ rprove_with_prop P pi0
| @rfrli x _ A pi0 => P (frl x A) /\ rprove_with_prop P pi0
| @rexsi x _ A _ _ pi0 => P (exs x A) /\ rprove_with_prop P pi0
| @rexse _ C _ _ pi1 pi2 => P C /\ nprove_with_prop P pi1 /\ rprove_with_prop P pi2
end.

Lemma rnprove_stronger : forall (P Q : formula -> Prop), (forall x, P x -> Q x) ->
   (forall l A (pi : nprove l A), nprove_with_prop P pi -> nprove_with_prop Q pi)
 * (forall l A (pi : rprove l A), rprove_with_prop P pi -> rprove_with_prop Q pi).
Proof. intros; apply rnprove_mutrect ; simpl ; intuition; eapply Forall_impl ; eassumption. Qed.

Proposition prove_with_prop_has_prop : forall (P : formula -> Prop),
 (forall A, P A↑ -> P A) ->
   (forall l A (pi : nprove l A), nprove_with_prop P pi -> Forall P (A :: l))
 * (forall l A (pi : rprove l A), rprove_with_prop P pi -> Forall P (A :: l)).
Proof.
intros P Hfup; apply rnprove_mutrect.
- intros l1 l2 A HP; inversion HP; repeat ((try apply Forall_app); try constructor); intuition.
- intros l B A pi1 HP1 pi2 HP2 pi; inversion_clear pi.
  constructor; intuition.
  now inversion H3.
- intros x l A u Hc pi1 HP1 pi; inversion_clear pi.
  constructor; intuition.
  now inversion H1.
- intros l A pi1 HP1 pi; intuition.
- intros l A N pi1 HP1 pi; inversion_clear pi.
  constructor; intuition.
  inversion_clear H1; now inversion H3.
- intros x l A pi1 HP1 pi; inversion_clear pi; intuition.
  constructor; intuition.
  inversion_clear H1.
  apply Forall_forall; intros C HC.
  apply in_map with (f:= esubs ⇑) in HC.
  specialize_Forall H3 with (C↑); intuition.
- intros x l A u Hc pi1 HP1 pi; inversion_clear pi; intuition.
  constructor; intuition.
  now inversion H1.
- intros l C x A pi1 HP1 pi2 HP2 pi; inversion_clear pi; intuition.
  constructor; intuition.
  now inversion H0.
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

Theorem subformula_prop :
   (forall l A (pi : nprove l A), nprove_with_prop (fun B => Exists (subform B) (A :: l)) pi)
 * (forall l A (pi : rprove l A), rprove_with_prop (fun B => Exists (subform B) (A :: l)) pi).
Proof. split; intros l A pi; apply lsubformula_prop. Qed.

Theorem subformula_prop_hered : forall (P : formula -> Prop),
 (forall A B, subform A B -> P B -> P A) ->
   (forall l A (pi : nprove l A), Forall P (A :: l) -> nprove_with_prop P pi)
 * (forall l A (pi : rprove l A), Forall P (A :: l) -> rprove_with_prop P pi).
Proof.
intros P HP; split; intros l A pi HF.
- assert (Hn := fst subformula_prop _ _ pi).
  apply rnprove_stronger with (Q := P) in Hn; [ assumption | ].
  intros C HC.
  apply Exists_exists in HC.
  destruct HC as [D [HD Hs]].
  specialize_Forall HF with D.
  apply HP with D; intuition.
- assert (Hr := snd subformula_prop _ _ pi).
  apply rnprove_stronger with (Q := P) in Hr; [ assumption | ].
  intros C HC.
  apply Exists_exists in HC.
  destruct HC as [D [HD Hs]].
  specialize_Forall HF with D.
  apply HP with D; intuition.
Qed.


(** * Examples *)
Section Examples.

Notation fvar := (@fvar vatom tatom fatom Nocon Nocon Icon Qcon nat).

Variable x y : vatom.

Goal forall A, rprove nil (imp (frl x (frl y A)) (frl y (frl x A))).
Proof.
rev_intros; case_analysis.
- rnow apply nfrle.
  replace (frl y A↑↑)
     with (subs y (evar 0) (frl y A↑↑))
    by rcauto.
  rnow apply nfrle then subst; rcauto.
- rcauto; rewrite subs_subs_closed; intuition.
  apply nfrle; intuition.
  replace (frl y A↑↑[evar 0//x]) with ((frl y A↑↑)[evar 0//x])
    by (simpl; case_analysis; intuition).
  apply nfrle; intuition.
Qed.

Variable f : tatom.
Variable P : fatom.

Goal rprove nil (imp (frl x (fvar P (tconstr f (tvar x :: nil) :: nil)))
                     (frl x (fvar P (tconstr f (tconstr f (tvar x :: nil) :: nil) :: nil)))).
Proof.
rev_intros; case_analysis.
replace (fvar P (tconstr f (tconstr f (evar 0 :: nil) :: nil) :: nil))
   with (subs x (tconstr f (evar 0 :: nil)) (fvar P (tconstr f (tvar x :: nil) :: nil)))
  by (simpl; case_analysis; intuition).
rnow apply nfrle.
Qed.

End Examples.


(** ** Hilbert style properties *)

Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "x ∉ A" := (~ x ∈ A) (at level 30).

Lemma frl_elim : forall A u x, closed u -> rprove (frl x A :: nil) (subs x u A).
Proof. intros A u x Hf; rev_intros; rnow apply (nfrle u). Qed.

Lemma frl_imp : forall A B x, rprove (frl x (imp A B) :: nil) (imp (frl x A) (frl x B)).
Proof. intros A B x; rev_intros.
apply (nimpe A↑[evar 0//x]).
- change (imp A↑[evar 0//x] B↑[evar 0//x])
    with ((imp A↑ B↑)[evar 0//x]).
  apply nfrle ; [ reflexivity | ] ; simpl.
  auto_nax.
- now apply rninj, nfrle, nax_hd.
Qed.

Lemma frl_nfree : forall A x, x ∉ A -> rprove (A :: nil) (frl x A).
Proof. intros A x Hnf; rev_intros; rnow rewrite nfree_subs. Qed.

Lemma Kcombi : forall A B, rprove nil (imp A (imp B A)).
Proof. rev_intros; auto_nax. Qed.

Lemma Scombi : forall A B C, rprove nil (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).
Proof.
rev_intros.
apply (nimpe B).
- apply (nimpe A); auto with term_db; auto_nax.
- apply rninj, (nimpe A); auto with term_db; auto_nax.
Qed.

End Proofs.
