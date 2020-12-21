(* Sequent Calculus for First-Order Additive Linear Logic *)

From Coq Require Import Wf_nat Lia.
Require Import foformulas_ext.

Set Implicit Arguments.


Parameter vatom : DecType.
Parameter tatom : Type.
Parameter fatom : Type.
Inductive Ncon := top_con.
Inductive Bcon := wth_con.
Inductive Qcon := frl_con.

Notation term := (@term vatom tatom nat).
Notation closed t := (tvars t = nil).
Notation fclosed r := (forall n, closed (r n)).
Notation "↑ r" := (felift (evar 0) r) (at level 25, format "↑ r").
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "⇑" := fup.
Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "x ∉ A" := (~ In x (freevars A)) (at level 30).

Notation formula := (@formula vatom tatom fatom Ncon Bcon Qcon nat).
(*
Notation top := (fnul nat top_con).
Notation wth := (fbin wth_con).
Notation frl := (fqtf frl_con).
*)
Notation "⟙" := (fnul nat top_con).
Infix "﹠" := (fbin wth_con) (at level 50).
Notation "∀" := (fqtf frl_con).

Hint Rewrite (@freevars_fup vatom tatom fatom Ncon Bcon Qcon) : term_db.
Hint Rewrite (@esubs_fup vatom tatom fatom Ncon Bcon Qcon) : term_db.
Hint Rewrite (@nfree_subs vatom tatom fatom Ncon Bcon Qcon nat) using intuition; fail : term_db.

Hint Resolve fclosed_fesubs : term_db.
Hint Resolve fclosed_felift : term_db.
Hint Rewrite (@subs_esubs vatom tatom fatom Ncon Bcon Qcon nat)
                        using try (intuition; fail);
                             (try apply no_ecapture_not_egenerated); try (intuition; fail);
                             (try apply fclosed_no_ecapture); intuition; fail : term_db.


(** * Proofs *)

(** Proofs *)
(** two-sided sequent calculus for first-order (additive) linear logic with connectives: 
    top, with, forall *)
Inductive prove : formula -> formula -> Type :=
| ax : forall A, prove A A
| topr : forall C, prove C ⟙
| wdgr { C A B } : prove C A -> prove C B -> prove C (A﹠B)
| wdgll { A C } : forall B, prove A C -> prove (A﹠B) C
| wdglr { A C } : forall B, prove A C -> prove (B﹠A) C
| frlr { x C A } : prove C↑ A↑[evar 0//x] -> prove C (∀x A)
| frll { x A C } : forall u, closed u -> prove A[u//x] C -> prove (∀x A) C.
Hint Constructors prove : term_db.

(** height of proofs *)
Fixpoint psize {A B} (pi : prove A B) : nat :=
match pi with
| ax _ => 1
| topr _ => 1
| wdgr pi1 pi2 => S (max (psize pi1) (psize pi2))
| wdgll _ pi1 => S (psize pi1)
| wdglr _ pi1 => S (psize pi1)
| frlr pi1 => S (psize pi1)
| frll _ _ pi1 => S (psize pi1)
end.

(** apply [r] in proof [pi] *)
Theorem pesubs r (Hc : fclosed r) C A (pi : prove C A) :
  { pi' : prove C⟦r⟧ A⟦r⟧ & psize pi' = psize pi }.
Proof.
revert r Hc; induction pi; intros r Hc;
  try (destruct (IHpi r) as [pi' Hs]);
  try (destruct (IHpi1 r) as [pi1' Hs1]);
  try (destruct (IHpi2 r) as [pi2' Hs2]); intuition.
- now exists (ax _).
- now exists (topr _).
- exists (wdgr pi1' pi2') ; simpl ; auto.
- exists (wdgll _ pi') ; simpl ; auto.
- exists (wdglr _ pi') ; simpl ; auto.
- clear pi' Hs; destruct (IHpi (↑r)) as [pi' Hs]; intuition.
  simpl; rewrite <- Hs; clear Hs.
  revert pi'; rnow idtac.
  revert pi'; rewrite <- 2 felift_esubs; intros pi'.
  exists (frlr pi'); reflexivity.
- simpl; rewrite <- Hs; clear Hs.
  revert pi'; rnow idtac.
  rewrite <- (tvars_tesubs_fclosed r Hc) in e.
  exists (frll _ e pi'); reflexivity.
Qed.


(** * Cut Elimination *)

Theorem cutr : forall A B C, prove A B -> prove B C -> prove A C.
Proof with try assumption.
enough (IH : forall n, forall A B C (pi1 : prove A B) (pi2 : prove B C),
          n = psize pi1 + psize pi2 -> prove A C)
  by (intros A B C pi1 pi2 ; apply (IH _ _ _ _ pi1 pi2 eq_refl)).
induction n as [n IH0] using lt_wf_rect; intros; subst.
assert (IH : forall A B C (pi1' : prove A B) (pi2' : prove B C),
               psize pi1' + psize pi2' < psize pi1 + psize pi2 -> prove A C)
  by (intros; eapply IH0; [ eassumption | reflexivity ]); clear IH0.
destruct pi2; intuition.
- apply wdgr.
  + apply (IH _ _ _ pi1 pi2_1); simpl; lia.
  + apply (IH _ _ _ pi1 pi2_2); simpl; lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                psize pi1' + psize pi2' < psize pi1 + psize (wdgll B pi2) -> prove A1 C0),
         D = A0﹠B -> prove A C)
    as IH2 by (eapply IH2; [ eassumption | reflexivity ]); clear.
  intros A D pi1 ; destruct pi1 ; intros ; inversion H ; subst ;
    try (constructor ; apply (IH _ _ _ pi1 (wdgll _ pi2)); simpl; lia).
  + now apply wdgll.
  + apply (IH _ _ _ pi1_1 pi2); simpl; lia.
  + apply (frll u)...
    apply (IH _ _ _ pi1 (wdgll _ pi2)); simpl; lia.
- enough (forall A D (pi1 : prove A D) A0 B C (pi2 : prove A0 C)
              (IH : forall A1 B0 C0 (pi1' : prove A1 B0) (pi2' : prove B0 C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (wdglr B pi2) -> prove A1 C0),
         D = B﹠A0 -> prove A C)
    as IH2 by (eapply IH2 ; [ eassumption | reflexivity ]) ; clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst;
    try (constructor; apply (IH _ _ _ pi1 (wdglr _ pi2)); simpl; lia).
  + now apply wdglr.
  + apply (IH _ _ _ pi1_2 pi2); simpl; lia.
  + apply (frll u)...
    apply (IH _ _ _ pi1 (wdglr _ pi2)); simpl; lia.
- destruct (pesubs ⇑ fclosed_fup pi1) as [pi1' Hs].
  apply frlr.
  apply (IH _ _ _ pi1' pi2); simpl; lia.
- enough (forall A D (pi1 : prove A D) x A0 C u e (pi2 : prove A0[u//x] C)
              (IH : forall A1 B C0 (pi1' : prove A1 B) (pi2' : prove B C0),
                 psize pi1' + psize pi2' < psize pi1 + psize (frll u e pi2) -> prove A1 C0),
         D = ∀ x A0 -> prove A C)
    as IH2 by (eapply IH2; [ eassumption | reflexivity ]); clear.
  intros A D pi1; destruct pi1; intros; inversion H; subst;
    try (constructor; apply (IH _ _ _ pi1 (frll _ e pi2)); simpl; lia).
  + now apply (frll u).
  + destruct (pesubs (u⇓) (fclosed_fesubs _ e) pi1) as [pi1' Hs].
    simpl in IH; rewrite <- Hs in IH; clear Hs.
    revert pi1' IH; rnow idtac.
    apply (IH _ _ _ pi1' pi2); lia.
  + apply (frll u)...
    apply (IH _ _ _ pi1 (frll _ e0 pi2)); simpl; lia.
Qed.


(** * Hilbert style properties *)

Lemma frl_elim : forall A u x, closed u -> prove (∀ x A) A[u//x].
Proof. intros A u x Hc; apply (frll u); auto with term_db. Qed.

Lemma frl_wth : forall A B x, prove (∀ x (A﹠B)) (∀ x A ﹠ ∀ x B).
Proof.
intros A B x.
repeat constructor; simpl;
  apply (frll (evar 0)); simpl; do 2 constructor.
Qed.

Lemma frl_nfree : forall A x, x ∉ A -> prove A (∀ x A).
Proof.
intros A x Hnf.
apply frlr.
rnow rewrite nfree_subs.
Qed.


(** * Other properties *)

(** Axiom expansion *)
Lemma ax_exp : forall A, prove A A.
Proof.
enough (Hn : forall n A, fsize A = n -> prove A A)
  by (intros A; eapply Hn; reflexivity).
induction n as [n IH] using lt_wf_rect; intros; subst.
destruct A; [ | destruct n | destruct b | destruct q ].
- apply ax.
- apply topr.
- apply wdgr; [ apply wdgll | apply wdglr ]; (eapply IH; [ | reflexivity ]); simpl; lia.
- apply frlr.
  rnow apply (frll (evar 0)).
Qed.
