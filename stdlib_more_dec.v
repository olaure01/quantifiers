(* Results missing in the standard library *)
(*   which require decidability *)

Require Export stdlib_more.
Require Import List dectype.

(* Results on lists of pairs (association lists) *)

Section Types.

Context {T1 : DecType} {T2 : Type}.
Variable x : T1.
Implicit Type L : list (T1 * T2).

Fixpoint remove_snd L :=
match L with
| nil => nil
| (y, F) :: TL => if eqb x y then remove_snd TL else (y, F) :: remove_snd TL
end.
Notation "L \" := (remove_snd L) (at level 9, format "L \").

Lemma remove_snd_remove L :
  remove eq_dt_dec x (map fst L) = map fst L\.
Proof.
induction L; simpl; [ reflexivity | rewrite IHL ]; destruct a; simpl.
repeat case_analysis; intuition.
Qed.

Lemma remove_snd_notin L :
  forall y a, x <> y -> In (y, a) L -> In (y, a) L\.
Proof.
induction L; simpl; intros y b Hneq Hin; [ assumption | destruct a ].
destruct Hin as [Hin|Hin]; case_analysis; intuition.
exfalso; apply Hneq.
now inversion Hin.
Qed.

Lemma snd_remove_snd L :
  incl (map snd L\) (map snd L).
Proof.
induction L; simpl; intros z Hz; intuition.
destruct a; simpl.
revert Hz; case_analysis; intros Hz; intuition.
Qed.

Lemma NoDup_remove_snd L :
  NoDup (map snd L) -> NoDup (map snd L\).
Proof.
induction L; simpl; intros Hnd; [ constructor | destruct a ].
inversion_clear Hnd.
case_analysis; intuition.
constructor; intuition.
apply snd_remove_snd in H2.
now apply H.
Qed.

Lemma NoDup_remove_snd2 L y i :
  NoDup (map snd L) -> In (y, i) L -> In i (map snd L\) -> In (y, i) L\.
Proof.
intros Hnd Hin1 Hin2.
apply remove_snd_notin; [ | apply snd_remove_snd in Hin2; intuition ].
intros Heq; symmetry in Heq; subst.
revert Hnd Hin1 Hin2; clear; induction L; [ intuition | ].
destruct a; simpl.
intros Hnd Hin1; inversion_clear Hnd; case_analysis; intros Hin2.
- symmetry in Heq; subst.
  apply IHL; intuition.
  exfalso; inversion H1; subst.
  apply H.
  now apply snd_remove_snd in Hin2.
- destruct Hin2 as [ Heq' | Hin2 ]; subst.
  + destruct Hin1 as [ Hin1 | Hin1 ].
    * inversion Hin1; subst; intuition.
    * apply H; now apply in_map with (f:= snd) in Hin1.
  + apply IHL in Hin2; intuition.
    exfalso; apply Heq; now inversion H1.
Qed.

End Types.

Notation "L ∖ x" := (remove_snd x L) (at level 18).

