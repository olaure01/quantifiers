(* Natural Deduction for First-Order Intuitionistic Logic *)

Require Import Lia.
Require Import stdlib_more.
Require Export foformulas.

Set Implicit Arguments.


(** * Proofs *)

Section Proofs.

Context { vatom : DecType } { tatom fatom : Type }.

Arguments tvar {_} {_} {T} _.

Notation term := (@term vatom tatom nat).
Notation closed t := (tvars t = nil).
Notation fclosed r := (forall n, closed (r n)).
Notation "↑ r" := (felift (dvar 0) r) (at level 25, format "↑ r").
Notation "v // ↓ k" := (fesubs k v) (at level 18, format "v // ↓ k").
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "⇑" := fup.
Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "x ∈ A" := (In x (freevars A)) (at level 30).

Notation formula := (@formula vatom tatom fatom Nocon Icon Qcon nat).
Notation fvar := (@fvar vatom tatom fatom Nocon Icon Qcon nat).

Hint Rewrite (@fsize_esubs vatom tatom fatom Nocon Icon Qcon) : term_db.
Hint Rewrite (@fsize_subs vatom tatom fatom Nocon Icon Qcon nat) : term_db.
Hint Rewrite (@tvars_tesubs_fclosed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@freevars_esubs_fclosed vatom tatom fatom Nocon Icon Qcon nat)
                 using intuition; fail : term_db.
Hint Rewrite (@subs_esubs vatom tatom fatom Nocon Icon Qcon nat)
                         using try (intuition; fail);
                              (try apply fclosed_notvars); intuition; fail : term_db.
Hint Rewrite <- (@lift_esubs vatom tatom fatom Nocon Icon Qcon) : term_db.
Hint Rewrite (@esubs_z_fup vatom tatom fatom Nocon Icon Qcon) : term_db.

Hint Resolve (@fclosed_felift vatom tatom) : term_db.
Hint Resolve (@fclosed_fesubs vatom tatom) : term_db.

(** Proofs *)
Inductive prove : list formula -> formula -> Type :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi { l A B } : prove (A :: l) B -> prove l (imp A B)
| impe { l B } : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli { x l A } : prove (map (fun F => F↑) l) A↑[dvar 0//x] -> prove l (frl x A)
| frle { x l A } : forall u, closed u -> prove l (frl x A) -> prove l (subs x u A)
| exsi { x l A } : forall u, closed u -> prove l (subs x u A) -> prove l (exs x A)
| exse { l C } : forall x A, prove l (exs x A) ->
                             prove (A↑[dvar 0//x] :: map (fun F => F↑) l) C↑ -> prove l C.
Hint Constructors prove : term_db.
Global Arguments impe { l B } _ _ _.
Global Arguments exse { l C } _ _ _.

Lemma ax_hd {l A} : prove (A :: l) A.
Proof. rewrite <- (app_nil_l (A :: l)); apply ax. Qed.

(** Normal Forms *)
Inductive nprove : list formula -> formula -> Type := (* neutral terms *)
| nax : forall l1 l2 A, nprove (l1 ++ A :: l2) A
| nimpe { l B } : forall A, nprove l (imp A B) -> rprove l A -> nprove l B
| nfrle { x l A } : forall u, closed u -> nprove l (frl x A) -> nprove l (subs x u A)
with rprove : list formula -> formula -> Type := (* normal forms *)
| rninj { l A } : nprove l A -> rprove l A
| rimpi { l A B } : rprove (A :: l) B -> rprove l (imp A B)
| rfrli { x l A } : rprove (map (esubs ⇑) l) A↑[dvar 0//x] -> rprove l (frl x A)
| rexsi { x l A } : forall u, closed u -> rprove l (subs x u A) -> rprove l (exs x A)
| rexse { l C } : forall x A,
                     nprove l (exs x A) ->
                     rprove (A↑[dvar 0//x] :: map (esubs ⇑) l) C↑ -> rprove l C.
Hint Constructors nprove rprove : term_db.
Global Arguments nimpe { l B } _ _ _.
Global Arguments rexse { l C } _ _ _ _.

Scheme nrprove_rect := Induction for nprove Sort Type
  with rnprove_rect := Induction for rprove Sort Type.
Combined Scheme rnprove_mutrect from nrprove_rect, rnprove_rect.

Lemma nax_hd {l A} : nprove (A :: l) A.
Proof. rewrite <- (app_nil_l (A :: l)); apply nax. Qed.
Hint Resolve nax_hd : term_db.

(* automatic tactic for application of the [nax] constructor *)
Ltac run_nax :=
  match goal with
  | |- nprove (?l1 ++ ?B :: ?l2) ?A => (try now apply nax);
         rewrite <- (app_nil_l l2); rewrite app_comm_cons, app_assoc; run_nax
  end.
Ltac auto_nax := rewrite <- (app_nil_l _); run_nax.

(* Apply all (reversible) introduction rules *)
Ltac rev_intros := repeat (repeat apply rimpi; repeat (apply rfrli; simpl)); apply rninj.

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


(** apply [r] in normal form *)
Theorem rnpesubs r (Hc : fclosed r) {l A} :
   (nprove l A -> nprove (map (esubs r) l) A⟦r⟧)
 * (rprove l A -> rprove (map (esubs r) l) A⟦r⟧).
Proof with try eassumption.
revert l A.
enough ((forall l A, nprove l A ->
                       forall r, fclosed r -> nprove (map (esubs r) l) A⟦r⟧)
      * (forall l A, rprove l A ->
                       forall r, fclosed r -> rprove (map (esubs r) l) A⟦r⟧))
  as He by (split; intros; apply He; assumption).
clear r Hc; apply rnprove_mutrect; intros; (try simpl in X);
  (try assert (IH1 := X r H)); (try assert (IH2 := X0 r H));
  (try (econstructor; (eassumption + intuition); fail)).
- rewrite map_app; apply nax.
- rnow idtac then rnow eapply nfrle.
- assert (fclosed (↑r0)) by rnow idtac.
  specialize X with (↑r0).
  revert X; rnow idtac.
  rewrite map_map, <- (map_ext _ _ (lift_esubs (dvar 0) _)), <- map_map in X0; intuition.
- rnow specialize X with r0 then rnow eapply (rexsi (tesubs r0 u)).
- assert (fclosed (↑r0)) as Hup by rnow idtac.
  assert (IH := X0 (↑r0) Hup); simpl in IH.
  rewrite map_map, <- (map_ext _ _ (lift_esubs (dvar 0) _)), <- map_map in IH.
  rnow eapply rexse.
Qed.

Lemma rpsubsz_r {l A x u} : closed u ->
  rprove (map (esubs ⇑) l) A↑[dvar 0//x] -> rprove l (subs x u A).
Proof.
intros Hc pi.
apply (rnpesubs (u//↓0)) in pi; [ | intuition ].
rnow simpl in pi then cbn in pi.
now rewrite map_map, (map_ext _ _ (esubs_z_fup _)), map_id in pi.
Qed.

Lemma rpsubsz_l {l A x u C} : closed u ->
  rprove (A↑[dvar 0//x] :: map (esubs ⇑) l) C↑ -> rprove (subs x u A :: l) C.
Proof.
intros Hc pi.
apply (rnpesubs (u//↓0)) in pi; [ | intuition ].
rnow simpl in pi then simpl in pi.
now rewrite map_map, (map_ext _ _ (esubs_z_fup _)), map_id in pi.
Qed.


(** * Normalization *)

Theorem denormalization :
  (forall l A, nprove l A -> prove l A) * (forall l A, rprove l A -> prove l A).
Proof. now apply rnprove_mutrect; intros; try (econstructor; eassumption). Qed.

Lemma weakening :
   (forall l A, nprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> nprove (l1 ++ l0 ++ l2) A)
 * (forall l A, rprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> rprove (l1 ++ l0 ++ l2) A).
Proof.
apply rnprove_mutrect ; intros ; try (econstructor; intuition; intuition ; fail) ; subst.
- enough (forall l l3, l1 ++ A :: l2 = l3 ++ l4 -> nprove (l ++ l3 ++ l0 ++ l4) A)
    as HI by (rewrite <- (app_nil_l (l3 ++ l0 ++ l4)) ; apply HI ; assumption) ; clear.
  induction l1; intros l l3 Heq; destruct l3; inversion Heq; subst; simpl.
  + simpl in Heq; subst; rewrite app_assoc; apply nax.
  + apply nax.
  + simpl in Heq; subst; rewrite app_comm_cons, 2 app_assoc; apply nax.
  + replace (l ++ f :: l3 ++ l0 ++ l4) with ((l ++ f :: nil) ++ l3 ++ l0 ++ l4)
      by (rewrite <- app_assoc ; reflexivity).
    now apply IHl1.
- apply rimpi; rewrite app_comm_cons; intuition.
- apply rfrli; rewrite ? map_app; apply X; rewrite map_app; reflexivity.
- apply (rexse x A).
  + now apply X.
  + rewrite ? map_app, app_comm_cons; apply X0 ; now rewrite map_app.
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
  + clear - Hsub ; intros D l B Hs pi1 pi2.
    rnow eapply (Hsub D).
  + rewrite <- (app_nil_l (map (esubs ⇑) l)) ; rewrite app_comm_cons ; rewrite <- (app_nil_l _).
    eapply weakening; [ | reflexivity ].
    now apply rnpesubs.
Qed.

Lemma frl_reduction : forall A x l, rprove l (frl x A) ->
  forall u, closed u -> rprove l (subs x u A).
Proof with try eassumption ; try reflexivity.
intros A x l pi.
remember (frl x A) as C; revert A x HeqC; induction pi;
  intros A1 x1 HeqC; inversion HeqC; subst; intros u Hc.
- apply rninj; eapply nfrle...
- eapply rpsubsz_r in pi...
- eapply rexse...
  rnow simpl in IHpi then rnow (eapply IHpi).
Qed.

Lemma exs_reduction : forall A x l, rprove l (exs x A) ->
(forall D l B, fsize D = fsize A -> rprove (D :: l) B -> rprove l D -> rprove l B) -> 
  forall C, rprove (A↑[dvar 0//x] :: map (esubs ⇑) l) C↑ -> rprove l C.
Proof.
intros A x l pi.
remember (exs x A) as A'; revert A x HeqA'; induction pi;
  intros A' x1 HeqA'; inversion HeqA'; subst; intros Hsub C pi2.
- eapply rexse; eassumption.
- eapply rpsubsz_l in pi2; [ | eassumption ].
  rnow apply (Hsub (A'[u//x1])).
- rnow simpl in IHpi.
  eapply rexse; [ eassumption | ].
  eapply IHpi ; [ reflexivity | | ].
  + clear - Hsub ; intros D l B Hs pi1 pi2.
    rnow eapply (Hsub D).
  + simpl ; rewrite <- (app_nil_l (subs x _ _ :: _)) ; rewrite app_comm_cons;
      rewrite <- (app_nil_l (map (esubs ⇑) _)) ; rewrite app_comm_cons.
    eapply weakening; [ | reflexivity ].
    apply (rnpesubs (↑⇑)) in pi2; intuition.
    rnow simpl in pi2 then simpl in pi2.
    now rewrite map_map, <- (map_ext _ _ (lift_esubs (dvar 0) _)), <- map_map in pi2.
Qed.

Lemma substitution : forall n m A, fsize A = n ->
   (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> fsize A < fsize B -> rprove (l1 ++ l2) A -> nprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : rprove (l1 ++ A :: l2) B),
      rsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B).
Proof with try eassumption ; try reflexivity ; try lia.
apply (lt_wf_double_rect (fun n m =>
 forall A, fsize A = n ->
   (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> fsize A < fsize B -> rprove (l1 ++ l2) A -> nprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : rprove (l1 ++ A :: l2) B),
      rsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B))) ;
  intros n m IHn IHm A HA ; (split ; [ split | ] ) ; subst ;
  intros B l1 l2 pi2 Hpi ; [ intros HF | | ] ; intros pi1 ;
  remember (l1 ++ A :: l2) as ll ; destruct pi2 ; subst ;
  simpl in IHm ; simpl in IHn ; simpl in Hpi ; try simpl in HF.
(* first statement *)
- clear - Heqll HF; revert l1 l2 Heqll HF; induction l0; intros l1 l2 Heqll HF;
    destruct l1; inversion Heqll; subst.
  + exfalso...
  + apply nax_hd.
  + apply nax.
  + apply IHl0 in H1...
    change (f :: l1) with (nil ++ (f :: nil) ++ l1) ; rewrite <- ? app_assoc.
    eapply weakening...
- assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  eapply nimpe ; eapply (IHm (S (nsize pi2 + rsize r))) ; simpl...
- apply nfrle...
  rnow eapply (IHm _ Hpi)...
(* second statement *)
- enough (forall l l1 l2, l0 ++ A0 :: l3 = l1 ++ A :: l2 ->
      rprove (l ++ l1 ++ l2) A -> rprove (l ++ l1 ++ l2) A0)
    as HI by (eapply (HI nil) ; eassumption) ; clear.
  induction l0; intros l l1 l2 Heq pi; destruct l1; inversion Heq; subst...
  + rewrite <- app_comm_cons ; apply rninj ; apply nax.
  + rewrite 2 app_assoc ; apply rninj ; apply nax.
  + rewrite <- app_comm_cons ; rewrite <- (app_nil_l l1) ;
      rewrite <- app_assoc ; rewrite app_comm_cons ; rewrite app_assoc.
    apply IHl0...
    rewrite <- ? app_assoc ; rewrite <- app_comm_cons...
- assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  destruct (Compare_dec.le_lt_dec (fsize (imp A0 B)) (fsize A)).
  + eapply IHm in IH1 ; eapply IHm in IH2...
    eapply imp_reduction...
    simpl in l ; intros D l' B' Heq pi1' pi2'.
    rewrite <- (app_nil_l _) in pi1'.
    refine (snd (IHn (fsize D) (S (rsize pi1')) _ _ _) _ _ _ pi1' _ pi2')...
  + apply rninj ; eapply nimpe ; eapply IHm...
- assert (nsize pi2 < S (nsize pi2)) as IH1 by lia.
  eapply IHm in IH1...
  eapply frl_reduction...
(* third statement *)
- refine (snd (fst (IHm _ _ _ _)) _ _ _ n _ _)...
- revert pi2 Hpi ; rewrite app_comm_cons ; intros pi2 Hpi.
  apply rimpi.
  refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _)...
  rewrite <- app_comm_cons ; rewrite <- (app_nil_l (l1 ++ l2)) ; rewrite app_comm_cons ;
    rewrite <- (app_nil_l _).
  eapply weakening...
- apply rfrli ; rewrite map_app.
  apply (rnpesubs ⇑) in pi1; intuition.
  revert pi1 pi2 Hpi ; rewrite ? map_app ; simpl ; intros pi1 pi2 Hpi.
  rnow refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _)...
- eapply rexsi...
  refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _)...
- rewrite <- (app_nil_l _) in pi1.
  assert (pi1' := snd weakening _ _ (snd (rnpesubs ⇑ fclosed_fup) pi1)
                  (A0↑[dvar 0//x] :: nil) nil _ eq_refl) ; simpl in pi1'.
  rewrite map_app in pi1' ; rewrite app_comm_cons in pi1'.
  revert pi2 pi1' Hpi ; rewrite ? map_app ; simpl ; rewrite app_comm_cons ;
    intros pi2 pi1' Hpi.
  assert (fsize (A↑) = fsize A) as Hup by (rnow idtac).
  eapply (snd (IHm _ Hpi _ Hup) _ _ _ pi2) in pi1'...
  destruct (Compare_dec.le_lt_dec (fsize (exs x A0)) (fsize A)).
  + eapply (snd (fst (IHm _ Hpi _ eq_refl)) _ _ _ n) in pi1...
    simpl in pi1' ; rewrite <- map_app in pi1'.
    eapply exs_reduction...
    simpl in l ; intros D l' B' Heq pi1'' pi2''.
    rewrite <- (app_nil_l _) in pi1''.
    refine (snd (IHn (fsize D) (S (rsize pi1'')) _ _ _) _ _ _ pi1'' _ pi2'')...
  + eapply rexse.
    * refine (fst (fst (IHm _ _ _ _ )) _ _ _ n _ _ _)...
    * rewrite map_app...
Qed.

Lemma smp_substitution : forall l A B, rprove l A -> rprove (A :: l) B -> rprove l B.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A B pi1 pi2.
rewrite <- (app_nil_l (A :: l)) in pi2 ; rewrite <- (app_nil_l l).
refine (snd (substitution (S (rsize pi2)) _ _ ) _ _ _ pi2 _ _)...
Qed.

Theorem normalization : forall l A, prove l A -> rprove l A.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A pi ; induction pi ;
   try (econstructor ; (idtac + econstructor) ; eassumption).
- eapply imp_reduction...
  clear ; intros ; eapply smp_substitution...
- eapply frl_reduction...
- eapply exs_reduction...
  clear ; intros ; eapply smp_substitution...
Qed.


(** * Sub-Formula Property *)

(** Sub-formula Relation *)
Inductive subform : formula -> formula -> Prop :=
| sub_id : forall A, subform A A
| sub_imp_l : forall A B C, subform A B -> subform A (imp B C)
| sub_imp_r : forall A B C, subform A B -> subform A (imp C B)
| sub_frl : forall A x u B, subform A (subs x u B) -> subform A (frl x B)
| sub_exs : forall A x u B, subform A (subs x u B) -> subform A (exs x B)
| sub_frl_n : forall A x B, subform A B↑[dvar 0//x] -> subform A (frl x B)
| sub_ex_n : forall A x B, subform A B↑[dvar 0//x] -> subform A (exs x B)
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
  apply (sub_frl _ (dvar 1)).
  rcauto; apply sub_id.
- eapply subform_trans; [ apply IHHs | ].
  apply sub_fup; simpl.
  apply (sub_exs _ (dvar 1)).
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

Variable x y : vatom.

Goal forall A, rprove nil (imp (frl x (frl y A)) (frl y (frl x A))).
Proof.
intros; rev_intros; case_analysis.
- rnow apply nfrle.
  replace (frl y A↑↑)
     with (subs y (dvar 0) (frl y A↑↑))
    by rcauto.
  rnow apply nfrle then subst; rcauto.
- rewrite subs_esubs, subs_subs_closed; intuition.
  apply nfrle; intuition.
  replace (frl y A↑↑[dvar 0//x]) with ((frl y A↑↑)[dvar 0//x])
    by (simpl; case_analysis; intuition).
  apply nfrle; intuition.
Qed.

Variable f : tatom.
Variable P : fatom.

Goal rprove nil (imp (frl x (fvar P (tconstr f (tvar x :: nil) :: nil)))
                     (frl x (fvar P (tconstr f (tconstr f (tvar x :: nil) :: nil) :: nil)))).
Proof.
intros; rev_intros; case_analysis.
replace (fvar P (tconstr f (tconstr f (dvar 0 :: nil) :: nil) :: nil))
   with (subs x (tconstr f (dvar 0 :: nil)) (fvar P (tconstr f (tvar x :: nil) :: nil)))
  by (simpl; case_analysis; intuition).
rnow apply nfrle.
Qed.

End Examples.


(** ** Hilbert style properties *)

Lemma frl_elim : forall A u x, closed u -> rprove (frl x A :: nil) (subs x u A).
Proof. intros A u x Hf; rev_intros; rnow apply (nfrle u). Qed.

Lemma frl_imp : forall A B x, rprove (frl x (imp A B) :: nil) (imp (frl x A) (frl x B)).
Proof. intros A B x; rev_intros.
apply (nimpe A↑[dvar 0//x]).
- change (imp A↑[dvar 0//x] B↑[dvar 0//x])
    with ((imp A↑ B↑)[dvar 0//x]).
  apply nfrle ; [ reflexivity | ] ; simpl.
  auto_nax.
- now apply rninj, nfrle, nax_hd.
Qed.

Lemma frl_nfree : forall A x, ~ x ∈ A -> rprove (A :: nil) (frl x A).
Proof. intros A x Hnf; rev_intros; rnow rewrite nfree_subs. Qed.

Lemma Kcombi : forall A B, rprove nil (imp A (imp B A)).
Proof. intros ; rev_intros; auto_nax. Qed.

Lemma Scombi : forall A B C, rprove nil (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).
Proof with auto with term_db.
intros ; rev_intros.
apply (nimpe B).
- apply (nimpe A)...
  auto_nax.
- apply rninj ; apply (nimpe A)...
  auto_nax.
Qed.

End Proofs.

