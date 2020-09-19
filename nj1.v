(* Natural Deduction for First-Order Intuitionistic Logic *)

From Coq Require Import Wf_nat Lia.

Require Import lib_files.List_more.

Require Export foformulas.

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

Inductive FQcon := frl_con.
Notation frl := (fqtf frl_con).

Notation formula := (@formula vatom tatom fatom Nocon Icon FQcon nat).

Hint Rewrite (@fsize_esubs vatom tatom fatom Nocon Icon FQcon) : term_db.
Hint Rewrite (@fsize_subs vatom tatom fatom Nocon Icon FQcon nat) : term_db.
Hint Rewrite (@tvars_tesubs_fclosed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@freevars_esubs_fclosed vatom tatom fatom Nocon Icon FQcon nat)
                 using intuition; fail : term_db.
Hint Rewrite (@subs_esubs vatom tatom fatom Nocon Icon FQcon nat)
                         using intuition; fail : term_db.
Hint Rewrite <- (@felift_esubs vatom tatom fatom Nocon Icon FQcon) : term_db.
Hint Rewrite (@esubs_fup vatom tatom fatom Nocon Icon FQcon) : term_db.

Hint Resolve fclosed_felift : term_db.
Hint Resolve fclosed_fesubs : term_db.


(** Proofs *)
Inductive prove : list formula -> formula -> Type :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi l A B : prove (A :: l) B -> prove l (imp A B)
| impe l B : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli x l A : prove l⇈ A↑[evar 0//x] -> prove l (frl x A)
| frle x l A : forall u, closed u -> prove l (frl x A) -> prove l (subs x u A).
Hint Constructors prove : term_db.
Global Arguments impe { l B }.

Lemma ax_hd {l A} : prove (A :: l) A.
Proof (ax nil l A).

(* This [weakening] lemma is not required in the development, see rather [nweakening] below *)
(* It is given here for comparison with alternative formalizations of Natural Deduction *)
Lemma weakening : forall l A, prove l A -> forall l0, prove (l ++ l0) A.
Proof.
intros l A pi; induction pi; intros; subst;
  try (econstructor; rewrite_all map_app; rewrite ? app_comm_cons; intuition; fail).
rewrite <- app_assoc, <- app_comm_cons; intuition.
Qed.
(* an alternative slightly more general statement:
Lemma weakening_middle : forall l A,
  prove l A -> forall l0 l1 l2, l = l1 ++ l2 -> prove (l1 ++ l0 ++ l2) A.
Proof.
intros l A pi; induction pi; intros; subst;
  try (econstructor; rewrite_all map_app; rewrite ? app_comm_cons; intuition; fail).
destruct (dichot_elt_app_inf _ _ _ _ _ H) as [ [? [? ?]] | [? [? ?]] ]; subst;
  rewrite ? (app_assoc _ _ (A::_)), <- ? (app_assoc _ (A::_)), <- ? app_comm_cons;
  intuition.
Qed.
*)


(** Normal Forms *)
Inductive nprove : list formula -> formula -> Type := (* neutral terms *)
| nax : forall l1 l2 A, nprove (l1 ++ A :: l2) A
| nimpe l B : forall A, nprove l (imp A B) -> rprove l A -> nprove l B
| nfrle x l A : forall u, closed u -> nprove l (frl x A) -> nprove l (subs x u A)
with rprove : list formula -> formula -> Type := (* normal forms *)
| rninj l A : nprove l A -> rprove l A
| rimpi l A B : rprove (A :: l) B -> rprove l (imp A B)
| rfrli x l A : rprove l⇈ A↑[evar 0//x] -> rprove l (frl x A).
Hint Constructors nprove rprove : term_db.
Global Arguments rfrli { x l A }.
Global Arguments nimpe { l B }.

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
  end.
Ltac auto_nax := rewrite <- (app_nil_l _); run_nax.

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
Qed.

Lemma rpsubsz {l A x u} : closed u ->
  rprove l⇈ A↑[evar 0//x] -> rprove l (subs x u A).
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
  try (econstructor; rewrite_all map_app; rewrite ? app_comm_cons; intuition; fail).
destruct (dichot_elt_app_inf _ _ _ _ _ H) as [ [? [? ?]] | [? [? ?]] ]; subst;
  rewrite ? (app_assoc _ _ (A::_)), <- ? (app_assoc _ (A::_)), <- ? app_comm_cons;
  intuition.
Qed.

Lemma substitution : forall l A B, rprove l A -> rprove (A :: l) B -> rprove l B.
Proof with try eassumption; try reflexivity; try lia.
pose (IH := (fun n m =>
 forall A, fsize A = n ->
   (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> fsize A < fsize B -> rprove (l1 ++ l2) A -> nprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : nprove (l1 ++ A :: l2) B),
      nsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B)
 * (forall B l1 l2 (pi : rprove (l1 ++ A :: l2) B),
      rsize pi < m -> rprove (l1 ++ l2) A -> rprove (l1 ++ l2) B))).
enough (forall n m, IH n m) as Hsub.
{ intros l A B pi1 pi2.
  rewrite <- (app_nil_l (A :: l)) in pi2; rewrite <- (app_nil_l l).
  refine (snd (Hsub _ (S (rsize pi2)) _ _) _ _ _ _ _ _); intuition. }
apply lt_wf_double_rect; unfold IH; clear IH; simpl;
 intros n m IHn IHm A HA; (split; [ split | ] ); subst;
 intros B l1 l2 pi2 Hpi; [ intros HF | | ]; intros pi1;
 remember (l1 ++ A :: l2) as ll; destruct pi2; subst; simpl in Hpi.
(* first statement *)
- destruct (dichot_elt_app_inf _ _ _ _ _ Heqll)
    as [ (l' & Heq0 & Heq) | (l' & Heq0 & Heq) ]; subst.
  + rewrite <- app_assoc; apply nax.
  + destruct l'; inversion Heq; subst.
    * exfalso; lia.
    * rewrite app_assoc; apply nax.
- assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  eapply nimpe; eapply (IHm (S (nsize pi2 + rsize r))); simpl...
- apply nfrle...
  rnow eapply (IHm _ Hpi)...
(* second statement *)
- enough (forall l l1 l2, l0 ++ A0 :: l3 = l1 ++ A :: l2 ->
      rprove (l ++ l1 ++ l2) A -> rprove (l ++ l1 ++ l2) A0)
    as HI by (eapply (HI nil); eassumption) ; clear.
  induction l0; intros l l1 l2 Heq pi; destruct l1; inversion Heq; subst...
  + rewrite <- app_comm_cons; apply rninj, nax.
  + rewrite 2 app_assoc; apply rninj, nax.
  + rewrite <- app_comm_cons, <- (app_nil_l l1), <- app_assoc, app_comm_cons, app_assoc.
    apply IHl0...
    rewrite <- ? app_assoc, <- app_comm_cons...
- assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  eapply IHm in IH2...
  assert ({fsize (imp A0 B) <= fsize A} + {fsize A < fsize (imp A0 B)}) as [ Ho | Ho ]
    by (case (CompareSpec2Type (Nat.compare_spec (fsize (imp A0 B)) (fsize A))); intros Ho;
          [ left | left | right ]; lia); simpl in Ho.
  + eapply IHm in IH1...
    inversion_clear IH1 as [ l' A' pi1' | l' A' B' pi1' | ].
    * apply rninj; eapply nimpe...
    * rewrite <- (app_nil_l _) in pi1'.
      refine (snd (IHn (fsize A0) (S (rsize pi1')) _ _ _) _ _ _ pi1' _ IH2)...
  + apply rninj, (nimpe A0)...
    eapply IHm...
- assert (nsize pi2 < S (nsize pi2)) as IH1 by lia.
  eapply IHm in IH1...
  inversion_clear IH1.
  + apply rninj; eapply nfrle...
  + now apply rpsubsz.
(* third statement *)
- refine (snd (fst (IHm _ _ _ _)) _ _ _ n _ _)...
- revert pi2 Hpi; rewrite app_comm_cons; intros pi2 Hpi.
  apply rimpi.
  refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _)...
  rewrite <- app_comm_cons, <- (app_nil_l (l1 ++ l2)), app_comm_cons, <- (app_nil_l _).
  eapply rweakening...
- apply rfrli; rewrite map_app.
  apply (rnpesubs ⇑) in pi1; intuition.
  revert pi1 pi2 Hpi; rewrite ? map_app; simpl; intros pi1 pi2 Hpi.
  rnow refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _)...
Qed.

Theorem normalization : forall l A, prove l A -> rprove l A.
Proof.
intros l A pi; induction pi; try (econstructor; (idtac + econstructor); eassumption).
- inversion_clear IHpi1.
  + apply rninj; eapply nimpe; eassumption.
  + eapply substitution; eassumption.
- inversion_clear IHpi.
  + apply rninj; now eapply nfrle.
  + now apply rpsubsz.
Qed.

End Proofs.
