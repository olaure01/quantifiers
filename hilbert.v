(* Hilbert system for Intuitionistic Logic with implication and quantifiers *)

Require Import List.
Require Import stdlib_more.
Require Import foformulas.

Set Implicit Arguments.


(** * Proofs *)

Section Proofs.

Context { vatom : DecType } { tatom fatom : Type }.

Arguments tvar {_} {_} {T} _.

Notation term := (@term vatom tatom Empty_set).
Notation closed t := (tvars t = nil).
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "y #[ x ] A" := (no_capture_at x y A) (at level 30, format "y  #[ x ]  A").

Notation formula := (@formula vatom tatom fatom Nocon Icon Qcon Empty_set).
Notation fvar := (@fvar vatom tatom fatom Nocon Icon Qcon Empty_set).
Notation imp := (fbin imp_con).
Notation frl := (fqtf frl_con).
Notation exs := (fqtf exs_con).
Infix "→" := (fbin imp_con) (at level 70, right associativity).

(** Proofs *)
Inductive hprove : formula -> Type :=
| hprove_K : forall A B, hprove (A → B → A)
| hprove_S : forall A B C, hprove ((A → B → C) → ((A → B) → A → C))
| hprove_MP : forall A B, hprove (A → B) -> hprove A -> hprove B
| hprove_INST : forall x A t, Forall (fun y => y #[x] A) (tvars t) ->
                   hprove (frl x A → A[t//x])
| hprove_FRL : forall x A B, ~ x ∈ A -> hprove ((frl x (A → B)) → A → frl x B)
| hprove_GEN : forall x A, hprove A -> hprove (frl x A)
| hprove_EINST : forall x A t, Forall (fun y => y #[x] A) (tvars t) ->
                   hprove (A[t//x] → exs x A)
| hprove_EXS : forall x A B, ~ x ∈ B -> hprove (frl x (A → B) → exs x A → B).

Lemma hprove_I A : hprove (A → A).
Proof. (* I = (S K) K *)
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K with (B := A → A).
- apply hprove_K.
Qed.

Lemma hprove_B A B C : hprove ((B → C) → (A → B) → A → C).
Proof. (* B = (S (K S)) K *)
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + eapply hprove_MP.
    * apply hprove_K.
    * apply hprove_S.
- apply hprove_K.
Qed.

Lemma hprove_C A B C : hprove ((A → B → C) → B → A → C).
Proof. (* C = (S ((S (K B)) S)) (K K) *)
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + eapply hprove_MP.
    * eapply hprove_MP.
      -- apply hprove_S.
      -- eapply hprove_MP.
         ++ apply hprove_K.
         ++ apply hprove_B.
    * apply hprove_S.
- eapply hprove_MP.
  + apply hprove_K.
  + apply hprove_K.
Qed.

Lemma hprove_K2 A B : hprove (B → A → A).
Proof. (* K2 = C K *)
eapply hprove_MP.
- apply hprove_C.
- apply hprove_K.
Qed.

Lemma hprove_W A B : hprove ((A → A → B) → A → B).
Proof. (* (S S) (S K) *)
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_S.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K.
Qed.

Lemma hprove_CUT B A C : hprove (A → B) -> hprove (B → C) -> hprove (A → C).
Proof. (* fun x y => (B y) x *)
intros pi1 pi2.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_B.
  + apply pi2.
- apply pi1.
Qed.

Lemma hprove_B2 A B C : hprove ((A → B) → (B → C) → A → C).
Proof. (* C B *)
eapply hprove_MP.
- apply hprove_C.
- apply hprove_B.
Qed.

End Proofs.

