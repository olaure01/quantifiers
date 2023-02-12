From Coq Require Import Lia.
From OLlibs Require Import List_Type.
From Quantifiers Require Import foformulas_ext nj1_frl.

Set Implicit Arguments.

Section Proofs.

Context { vatom : DecType } { tatom fatom : Type }.

Notation term := (@term vatom tatom nat).
Notation formula := (@formula vatom tatom fatom Nocon Nocon Icon FQcon nat).
Notation frl := (fqtf frl_con).
Notation closed t := (tvars t = nil).
Notation rclosed r := (forall n, closed (r n)).
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "⇑" := fup.
Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "l ⇈" := (map (fun F => F↑) l) (at level 8, format "l ⇈").

Notation "'ε' k" := (evar k) (at level 5, format "ε k").

Implicit Type A : formula.

(* Suggested by Dominik Kirst *)
Lemma frli_fresh k x l A : list_max (map eigen_max (A :: l)) < k ->
  prove l A[evar k//x] -> prove l (frl x A).
Proof.
intros Hmax pi; apply denormalization, rfrli; apply normalization in pi.
remember (fun n => if Nat.eqb n k then evar 0 else evar (S n) : term) as rk.
assert (rclosed rk) as Hc by (now intros n; rewrite Heqrk; destruct (n =? k)).
assert (map (esubs rk) (A :: l) = map (fun F => F↑) (A :: l)) as Hrkfup.
{ apply map_ext_in_inf; intros a Hin.
  apply esubs_ext_max; intros n Hle.
  apply list_max_lt_inf in Hmax; [ | intros Hl; inversion Hl ].
  apply (in_inf_map eigen_max), (Forall_inf_forall Hmax) in Hin.
  assert (n <> k) as Hneq by lia.
  now subst rk; apply Nat.eqb_neq in Hneq; rewrite_all Hneq. }
apply (rnpesubs rk) in pi; auto.
rewrite subs_esubs in pi; auto.
injection Hrkfup; intros Hl HA; rewrite Hl, HA in pi.
now subst rk; simpl in pi; rewrite Nat.eqb_refl in pi.
Qed.

Lemma frli_gentzen x l A :
  { k & list_max (map eigen_max (A :: l)) < k & prove l A[evar k//x] -> prove l (frl x A) }.
Proof. exists (S (list_max (map eigen_max (A :: l)))); [ | apply frli_fresh ]; lia. Qed.

(*
Notation "x ∉ A" := (~ In x (freevars A)) (at level 30).
Example gentzen_simulation x l A : x ∉ A -> prove l A -> prove l (frl x A).
Proof.
intros Hf pi.
destruct (frli_gentzen x l A) as [k Hfresh Hfrl]; apply Hfrl; clear Hfrl.
now rewrite nfree_subs.
Qed.
*)

End Proofs.
