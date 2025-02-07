(* Sequent Calculus for First- and Second-Order Additive Linear Logic *)

From Stdlib Require Import Wf_nat Lia.
From Quantifiers Require Import formulas.

Set Implicit Arguments.


Parameter vatom : DecType.
Parameter tatom : Type.
Parameter satom : DecType.
Parameter fatom : Type.
Inductive Ncon := top_con.
Inductive Bcon := wth_con.
Inductive Qcon := frl_con.

Notation term := (@term vatom tatom nat).
Notation tclosed t := (tvars t = nil).
Notation rtclosed r := (forall n, tclosed (r n)).
Notation "↑ r" := (felift (evar 0) r) (at level 25, format "↑ r").
Notation "↑2 r" := (feslift (sevar _ 0) r) (at level 25, format "↑2 r").
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").
Notation "F ⇓2" := (fessubs F) (at level 18, format "F ⇓2").
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").
Notation "A ⟦ r ⟧2" := (essubs r A) (at level 8, left associativity, format "A ⟦ r ⟧2").
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "A [ F // X ]2" := (ssubs X F A) (at level 8, format "A [ F // X ]2").
Notation "⇑" := fup.
Notation "⇑2" := (sfup nat).
Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "A ↑2" := (A⟦⇑2⟧2) (at level 8, format "A ↑2").
Notation fclosed A := (freevars A = nil).
Notation rfclosed r := (forall n, fclosed (r n)).
Notation sclosed A := (sfreevars A = nil).
Notation rsclosed r := (forall n, sclosed (r n)).

Notation formula := (@formula vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon nat nat).
Notation top := (fnul nat nat top_con).
Notation wth := (fbin wth_con).
Notation frl := (fqtf frl_con).
Notation frl2 := (sqtf frl_con).
Definition evar_nat := (@evar vatom tatom nat).
Coercion evar_nat : nat >-> term.
Definition sevar_nat := (@sevar vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon nat nat).
Coercion sevar_nat : nat >-> formula.
Notation sevar := (sevar nat).

#[local] Hint Resolve closed_fesubs : term_db.
#[local] Hint Resolve closed_felift : term_db.
#[local] Hint Resolve fclosed_fessubs : term_db.
#[local] Hint Resolve sclosed_fessubs : term_db.
#[local] Hint Resolve fclosed_feslift : term_db.
#[local] Hint Resolve sclosed_feslift : term_db.

#[local] Hint Rewrite (@felift_esubs vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon) : term_db.
#[local] Hint Rewrite (@feslift_esubs vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon) : term_db.
#[local] Hint Rewrite (@felift_essubs vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon) : term_db.
#[local] Hint Rewrite (@feslift_essubs vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon) : term_db.
#[local] Hint Rewrite (@esubs_fup vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon) : term_db.
#[local] Hint Rewrite (@essubs_fup vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon) : term_db.
#[local] Hint Rewrite (@subs_esubs vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon)
                        using try tauto; auto with term_db : term_db.
#[local] Hint Rewrite (@ssubs_esubs vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon)
                        using try tauto; auto with term_db : term_db.
#[local] Hint Rewrite (@subs_essubs vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon)
                        using try tauto; auto with term_db : term_db.
#[local] Hint Rewrite (@ssubs_essubs vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon)
                        using try tauto; auto with term_db : term_db.
#[local] Hint Rewrite (@freevars_fup vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon) : term_db.
#[local] Hint Rewrite (@sfreevars_fup vatom tatom satom fatom Ncon Nocon Bcon Qcon Qcon) : term_db.


(** * Proofs *)

(** Proofs *)
(** two-sided sequent calculus for (additive) linear logic with connectives: top, with, forall, forall2 *)
Inductive prove : formula -> formula -> Type :=
| ax A : prove A A
| topr C : prove C top
| wdgr C A B : prove C A -> prove C B -> prove C (wth A B)
| wdgll A C B : prove A C -> prove (wth A B) C
| wdglr A C B : prove A C -> prove (wth B A) C
| frlr [x C A] : prove (C↑) A↑[0//x] -> prove C (frl x A)
| frll [x A C] u : tclosed u -> prove A[u//x] C -> prove (frl x A) C
| frl2r [X C A] : prove (C↑2) A↑2[0//X]2 -> prove C (frl2 X A)
| frl2l [X A C] F : fclosed F -> sclosed F -> prove A[F//X]2 C -> prove (frl2 X A) C.
#[local] Hint Constructors prove : term_db.


(** height of proofs *)
Fixpoint psize A B (pi : prove A B) : nat :=
match pi with
| ax _ | topr _ => 1
| wdgr pi1 pi2 => S (max (psize pi1) (psize pi2))
| wdgll _ pi1 | wdglr _ pi1 => S (psize pi1)
| frlr pi1 | frll _ _ pi1 | frl2r pi1 | frl2l _ _ _ pi1 => S (psize pi1)
end.


(** proofs with atomic axioms *)
Fixpoint atomic_proof A B (pi : prove A B) : Prop :=
match pi with
| ax A => atomic A
| topr _ => True
| wdgr pi1 pi2 => atomic_proof pi1 /\ atomic_proof pi2
| wdgll _ pi1 | wdglr _ pi1 | frlr pi1 | frll _ _ pi1 | frl2r pi1 | frl2l _ _ _ pi1 => atomic_proof pi1
end.


(** apply [r] in proof [pi] *)
Theorem pesubs r (Hc : rtclosed r) C A (pi : prove C A) : { pi' : prove C⟦r⟧ A⟦r⟧ & psize pi' = psize pi }.
Proof.
induction pi in r, Hc |- *;
  try (destruct (IHpi r) as [pi' Hs]);
  try (destruct (IHpi1 r) as [pi1' Hs1]);
  try (destruct (IHpi2 r) as [pi2' Hs2]); trivial.
- now exists (ax _).
- now exists (topr _).
- exists (wdgr pi1' pi2'). cbn. auto.
- exists (wdgll _ pi'). cbn. auto.
- exists (wdglr _ pi'). cbn. auto.
- clear pi' Hs. destruct (IHpi (↑r)) as [pi' Hs]; [ intuition | ].
  cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  exists (frlr pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  rewrite <- (tvars_tesubs_closed r _ Hc) in e.
  exists (frll _ e pi'). reflexivity.
- clear pi' Hs. destruct (IHpi r) as [pi' Hs]; [ intuition | ].
  cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  exists (frl2r pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  rewrite <- (freevars_esubs_closed r) in e by assumption.
  rewrite <- (sfreevars_esubs r) in e0.
  exists (frl2l _ e e0 pi'). reflexivity.
Qed.

Theorem pessubs r (Hcf : rfclosed r) (Hcs : rsclosed r) C A (pi : prove C A) :
  { pi' : prove C⟦r⟧2 A⟦r⟧2 & psize pi' = psize pi }.
Proof.
induction pi in r, Hcf, Hcs |- *;
  try (destruct (IHpi r) as [pi' Hs]);
  try (destruct (IHpi1 r) as [pi1' Hs1]);
  try (destruct (IHpi2 r) as [pi2' Hs2]); trivial.
- now exists (ax _).
- now exists (topr _).
- exists (wdgr pi1' pi2'). cbn. auto.
- exists (wdgll _ pi'). cbn. auto.
- exists (wdglr _ pi'). cbn. auto.
- clear pi' Hs. destruct (IHpi (fun n => (r n)↑)) as [pi' Hs]; rcauto.
  cbn. rewrite <- Hs. clear Hs.
  rnow (rnow revert pi').
  exists (frlr pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  exists (frll _ e pi'). reflexivity.
- clear pi' Hs. destruct (IHpi (↑2r)) as [pi' Hs]; [ rcauto | rcauto | ].
  cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  exists (frl2r pi'). reflexivity.
- cbn. rewrite <- Hs. clear Hs.
  rnow revert pi'.
  rewrite <- (freevars_essubs_closed _ _ Hcf) in e.
  rewrite <- (sfreevars_essubs_closed _ _ Hcs) in e0.
  exists (frl2l _ e e0 pi'). reflexivity.
Qed.


(** * Cut Elimination *)

Theorem cutr A B C : prove A B -> prove B C -> prove A C.
Proof.
enough (forall n, forall A B C (pi1 : prove A B) (pi2 : prove B C), n = psize pi1 + psize pi2 -> prove A C) as IH
  by (intros pi1 pi2; apply (IH _ _ _ _ pi1 pi2 eq_refl)). clear A B C.
induction n as [n IH0] using lt_wf_rect; intros; subst.
assert (forall A B C (pi1' : prove A B) (pi2' : prove B C),
          psize pi1' + psize pi2' < psize pi1 + psize pi2 -> prove A C) as IH
  by (intros; eapply IH0; [ eassumption | reflexivity ]); clear IH0.
destruct pi2; intuition.
- apply wdgr.
  + apply (IH _ _ _ pi1 pi2_1). cbn. lia.
  + apply (IH _ _ _ pi1 pi2_2). cbn. lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                psize pi1' + psize pi2' < psize pi1 + psize (wdgll B pi2) -> prove A1 C0),
         D = wth A0 B -> prove A C) as IH2
    by (eapply IH2; [ eassumption | reflexivity ]); clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst;
    try (constructor; apply (IH _ _ _ pi1 (wdgll _ pi2)); cbn; lia).
  + now apply wdgll.
  + apply (IH _ _ _ pi1_1 pi2). cbn. lia.
  + apply (frll u); [ assumption | ].
    apply (IH _ _ _ pi1 (wdgll _ pi2)). cbn. lia.
  + apply (frl2l F); [ assumption | assumption | ].
    apply (IH _ _ _ pi1 (wdgll _ pi2)). cbn. lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (wdglr B pi2) -> prove A1 C0),
         D = wth B A0 -> prove A C) as IH2
    by (eapply IH2 ; [ eassumption | reflexivity ]); clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst;
    try (constructor; apply (IH _ _ _ pi1 (wdglr _ pi2)); cbn; lia).
  + now apply wdglr.
  + apply (IH _ _ _ pi1_2 pi2). cbn. lia.
  + apply (frll u); [ assumption | ].
    apply (IH _ _ _ pi1 (wdglr _ pi2)). cbn. lia.
  + apply (frl2l F); [ assumption | assumption | ].
    apply (IH _ _ _ pi1 (wdglr _ pi2)). cbn. lia.
- destruct (pesubs ⇑ closed_fup pi1) as [pi1' Hs].
  apply frlr, (IH _ _ _ pi1' pi2). cbn. lia.
- enough (forall A D (pi1 : prove A D) x A0 C u e (pi2 : prove A0[u//x] C)
              (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (frll u e pi2) -> prove A1 C0),
         D = frl x A0 -> prove A C) as IH2
    by (eapply IH2; [ eassumption | reflexivity ]); clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst;
    try (constructor; apply (IH _ _ _ pi1 (frll _ e pi2)); cbn; lia).
  + now apply (frll u).
  + destruct (pesubs (u⇓) (closed_fesubs _ e) pi1) as [pi1' Hs].
    simpl in IH. rewrite <- Hs in IH. clear Hs.
    rnow revert pi1' IH.
    apply (IH _ _ _ pi1' pi2). lia.
  + apply (frll u); [ assumption | ].
    apply (IH _ _ _ pi1 (frll _ e0 pi2)). cbn. lia.
  + apply (frl2l F); [ assumption | assumption | ].
    apply (IH _ _ _ pi1 (frll _ e1 pi2)). cbn. lia.
- destruct (pessubs ⇑2 fclosed_sfup sclosed_sfup pi1) as [pi1' Hs].
  apply frl2r, (IH _ _ _ pi1' pi2). cbn. lia.
- enough (forall A D (pi1 : prove A D) X A0 C F e e' (pi2 : prove A0[F//X]2 C)
              (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (frl2l F e e' pi2) -> prove A1 C0),
         D = frl2 X A0 -> prove A C) as IH2
    by (eapply IH2; [ eassumption | reflexivity ]); clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst;
    try (constructor; apply (IH _ _ _ pi1 (frl2l _ e e' pi2)); cbn; lia).
  + now apply (frl2l F).
  + apply (frll u); [ assumption | ].
    apply (IH _ _ _ pi1 (frl2l _ e0 e' pi2)). cbn. lia.
  + destruct (pessubs (F⇓2) (fclosed_fessubs _ e) (sclosed_fessubs _ e') pi1) as [pi1' Hs].
    simpl in IH. rewrite <- Hs in IH. clear Hs.
    rnow revert pi1' IH.
    apply (IH _ _ _ pi1' pi2). lia.
  + apply (frl2l F); [ assumption | assumption | ].
    apply (IH _ _ _ pi1 (frl2l _ e1 e' pi2)). cbn. lia.
Qed.


(** * Axiom expansion *)

Lemma ax_gen_size A : { pi : prove A A | atomic_proof pi & psize pi < 2 * fsize A }.
Proof.
enough (Hn : forall n A, fsize A = n -> { pi : prove A A | atomic_proof pi & psize pi < 2 * fsize A })
  by (eapply Hn; reflexivity).
clear A. intro n. induction n as [n IH] using lt_wf_rect. intros A <-.
destruct A; [ | | | destruct n | destruct n | destruct b | destruct q | destruct q ].
- exists (ax _); [ constructor | cbn; lia ].
- exists (ax _); [ constructor | cbn; lia ].
- exists (ax _); [ constructor | cbn; lia ].
- exists (topr _); [ constructor | cbn; lia ].
- assert (fsize A1 < fsize (wth A1 A2)) as Hs1 by (cbn; lia).
  destruct (IH _ Hs1 _ eq_refl) as [pi1 Hat1 Hsize1].
  assert (fsize A2 < fsize (wth A1 A2)) as Hs2 by (cbn; lia).
  destruct (IH _ Hs2 _ eq_refl) as [pi2 Hat2 Hsize2].
  exists (wdgr (wdgll A2 pi1) (wdglr A1 pi2)); [ constructor; assumption | cbn; lia ].
- assert (fsize (A↑[0//c]) < fsize (frl c A)) as Hs.
  { rewrite fsize_subs, fsize_esubs. cbn. lia. }
  destruct (IH _ Hs _ eq_refl) as [pi Hat Hsize].
  exists (frlr (frll 0 eq_refl pi : prove ((frl c A)↑) _)); [ assumption | cbn in *; lia ].
- assert (fsize (A↑2[0//c]2) < fsize (frl2 c A)) as Hs.
  { rewrite fsize_ssubs_atomic, fsize_sfup by constructor. cbn. lia. }
  destruct (IH _ Hs _ eq_refl) as [pi Hat Hsize].
  exists (frl2r (frl2l 0 eq_refl eq_refl pi : prove ((frl2 c A)↑2) _)); [ assumption | cbn in *; lia ].
Qed.

Lemma ax_gen A : prove A A.
Proof. apply (ax_gen_size A). Qed.

Lemma ax_exp A B : prove A B -> { pi : prove A B | atomic_proof pi }.
Proof.
intros pi0. induction pi0.
- destruct (ax_gen_size A) as [pi Hat _].
  exists pi. exact Hat.
- exists (topr _). constructor.
- destruct IHpi0_1 as [pi1 Hat1], IHpi0_2 as [pi2 Hat2].
  exists (wdgr pi1 pi2). constructor; assumption.
- destruct IHpi0 as [pi Hat].
  exists (wdgll B pi). assumption.
- destruct IHpi0 as [pi Hat].
  exists (wdglr B pi). assumption.
- destruct IHpi0 as [pi Hat].
  exists (frlr pi). assumption.
- destruct IHpi0 as [pi Hat].
  exists (frll _ e pi). assumption.
- destruct IHpi0 as [pi Hat].
  exists (frl2r pi). assumption.
- destruct IHpi0 as [pi Hat].
  exists (frl2l _ e e0 pi). assumption.
Qed.


(** * Hilbert style properties *)

Lemma frl_elim A u x : tclosed u -> prove (frl x A) A[u//x].
Proof. intros Hc. apply (frll u), ax_gen. exact Hc. Qed.

Lemma frl_wth A B x : prove (frl x (wth A B)) (wth (frl x A) (frl x B)).
Proof. repeat constructor; cbn; apply (frll 0); cbn; constructor; apply ax_gen. Qed.

Lemma frl_nfree A x : ~ In x (freevars A) -> prove A (frl x A).
Proof. intros Hnf. apply frlr. rewrite nfree_subs; [ apply ax_gen | rcauto ]. Qed.
