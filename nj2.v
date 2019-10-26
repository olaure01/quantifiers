(* Sequent Calculus for Second-Order Propositional Additive Linear Logic *)

Require Import PeanoNat.
Require Import Lia.
Require Import List.

Create HintDb term_db.

Tactic Notation "rnow" tactic(t) :=
  t ; simpl ; autorewrite with term_db in * ; simpl ; intuition.
Tactic Notation "rnow" tactic(t) "then" tactic(t1) :=
  t ; simpl ; autorewrite with term_db in * ; simpl ; intuition t1 ; simpl ; intuition.

Lemma ltb_S : forall n m, (S n <? S m) = (n <? m).
Proof. reflexivity. Qed.
Hint Rewrite ltb_S : term_db.


(** * Different kinds of atoms *)

Parameter atom : Type. (* second-order constants *)
Parameter vatom : Type. (* variables for quantification *)
Parameter beq_vat : vatom -> vatom -> bool. (* boolean equality on [vatom] *)
Parameter beq_eq_vat : forall a b, beq_vat a b = true <-> a = b.
   (* equality specification for [vatom] *)

(* [vatom] presented as a type with Boolean equality *)
Module vatomBoolEq <: Equalities.UsualBoolEq.
Definition t := vatom.
Definition eq := @eq vatom.
Definition eqb := beq_vat.
Definition eqb_eq := beq_eq_vat.
End vatomBoolEq.
Module vatomEq := Equalities.Make_UDTF vatomBoolEq.
Module vatomFacts := Equalities.BoolEqualityFacts vatomEq.
Import vatomFacts.

Ltac case_analysis :=
match goal with
| |- context f [?x =? ?y] => case_eq (x =? y)
| |- context f [?x <? ?y] => case_eq (x <? y)
| |- context f [?x ?= ?y] => case_eq (x ?= y)
| |- context f [beq_vat ?x ?y] => case_eq (beq_vat x y)
| |- context f [vatomEq.eq_dec ?x  ?y] => case_eq (vatomEq.eq_dec x y)
end.
Ltac rcauto := simpl ; autorewrite with term_db in * ; simpl ; rnow case_analysis.

Lemma in_rmv : forall X Y, beq_vat Y X = false -> forall l,
  In X l -> In X (remove vatomEq.eq_dec Y l).
Proof.
induction l ; auto ; intros Hi.
inversion Hi ; subst ; simpl.
- destruct (vatomEq.eq_dec Y X) ; intuition.
  subst ; rewrite eqb_refl in H ; inversion H.
- destruct (vatomEq.eq_dec Y a) ; intuition.
Qed.
Hint Resolve in_rmv : term_db.



(** * Formulas *)

(** formulas *)
(** second-order formulas *)
Inductive formula :=
| var : vatom -> formula
| dvar : nat -> formula
| cst : atom -> formula
| imp : formula -> formula -> formula
| frl : vatom -> formula -> formula
| exs : vatom -> formula -> formula.

Ltac formula_induction A :=
  (try intros until A) ;
  let X := fresh "X" in
  let K := fresh "k" in
  let P := fresh "P" in
  let A1 := fresh A in
  let A2 := fresh A in
  let Y := fresh "X" in
  induction A as [ X | K | P | A1 A2 | Y A | Y A ] ; simpl ; intros ;
    try (f_equal ; intuition) ; try ((rnow idtac) ; fail) ; try (rcauto ; fail).


(** size of formulas *)
Fixpoint fsize A :=
match A with
| var _ => 1
| dvar _ => 1
| cst _ => 1
| imp B C => S (fsize B + fsize C)
| frl _ B => S (fsize B)
| exs _ B => S (fsize B)
end.


(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X => var X
| dvar n => if n <? k then dvar n else dvar (S n)
| cst R => cst R
| imp B C => imp (fup k B) (fup k C)
| frl X B => frl X (fup k B)
| exs X B => exs X (fup k B)
end.
Notation fupz := (fup 0).

Lemma fsize_fup : forall k A, fsize (fup k A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_fup : term_db.

Lemma fup_fup_com : forall k A,
  fup (S k) (fupz A) = fupz (fup k A).
Proof. formula_induction A. Qed.
Hint Rewrite fup_fup_com : term_db.



(** substitutes [formula] [F] for variable [X] in [formula] [A] (capture is possible) *)
Fixpoint subs X F A :=
match A with
| dvar k => dvar k
| var Y => if (beq_vat Y X) then F else var Y
| cst R => cst R
| imp B C => imp (subs X F B) (subs X F C)
| frl Y B as C => if (beq_vat Y X) then C else frl Y (subs X F B)
| exs Y B as C => if (beq_vat Y X) then C else exs Y (subs X F B)
end.

Lemma fsize_subs_dvar : forall k X A, fsize (subs X (dvar k) A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_subs_dvar : term_db.

Lemma fup_subs_com : forall k X F A,
  fup k (subs X F A) = subs X (fup k F) (fup k A).
Proof. now formula_induction A ; rcauto ; f_equal. Qed.
Hint Rewrite fup_subs_com : term_db.



(** substitutes [formula] [F] for index [n] in [formula] [A] and decreases indexes above [n] *)
Fixpoint nsubs n F A :=
match A with
| var X => var X
| dvar k => match n ?= k with
            | Eq => F
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| cst R => cst R
| imp B C => imp (nsubs n F B) (nsubs n F C)
| frl X B => frl X (nsubs n F B)
| exs X B => exs X (nsubs n F B)
end.

Lemma nsubs_fup_com : forall k F A,
  nsubs (S k) (fupz F) (fupz A) = fupz (nsubs k F A).
Proof. formula_induction A ; rcauto.
now destruct k0 ; destruct k ; intuition.
Qed.
Hint Rewrite nsubs_fup_com : term_db.


Fixpoint freevars A :=
match A with
| var X => X :: nil
| dvar _ => nil
| cst _ => nil
| imp B C => (freevars B) ++ (freevars C)
| frl X B => remove vatomEq.eq_dec X (freevars B)
| exs X B => remove vatomEq.eq_dec X (freevars B)
end.
Notation closed A := (freevars A = nil).

Lemma closed_nofreevars : forall A X, closed A -> ~ In X (freevars A).
Proof. intros A X Hc Hin ; now rewrite Hc in Hin. Qed.

Lemma freevars_fup : forall k A, freevars (fup k A) = freevars A.
Proof. formula_induction A. Qed.
Hint Rewrite freevars_fup : term_db.

Lemma freevars_nsubs : forall n F, closed F -> forall A,
  freevars (nsubs n F A) = freevars A.
Proof. formula_induction A. Qed.
Hint Rewrite freevars_nsubs using assumption : term_db.

Lemma nfree_subs : forall X F A, ~ In X (freevars A) -> subs X F A = A.
Proof. formula_induction A ; rcauto ; try now f_equal.
now apply vatomEq.eqb_eq in H.
Qed.
Hint Rewrite nfree_subs using try (intuition ; fail) ;
                              (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma nsubs_subs_com : forall X F n G, ~ In X (freevars G) -> forall A,
  nsubs n G (subs X F A) = subs X (nsubs n G F) (nsubs n G A).
Proof. now formula_induction A ; rcauto ; f_equal. Qed.
Hint Rewrite nsubs_subs_com using try (intuition ; fail) ;
                                  (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma nsubs_z_fup : forall F A, nsubs 0 F (fupz A) = A.
Proof. formula_induction A. Qed.
Hint Rewrite nsubs_z_fup : term_db.



(** * Proofs *)

(** Proofs *)
Inductive prove : list formula -> formula -> Type :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi { l A B } : prove (A :: l) B -> prove l (imp A B)
| impe { l B } : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli { X l A } : prove (map fupz l) (subs X (dvar 0) (fupz A)) -> prove l (frl X A)
| frle { X l A } : forall C, closed C -> prove l (frl X A) -> prove l (subs X C A)
| exsi { X l A } : forall C, closed C -> prove l (subs X C A) -> prove l (exs X A)
| exse { X l C } : forall A, prove l (exs X A) ->
                             prove (subs X (dvar 0) (fupz A) :: map fupz l) (fupz C) -> prove l C.
Hint Constructors prove : term_db.

(** Normal Forms *)
Inductive nprove : list formula -> formula -> Type := (* neutral terms *)
| nax : forall l1 l2 A, nprove (l1 ++ A :: l2) A
| nimpe { l B } : forall A, nprove l (imp A B) -> rprove l A -> nprove l B
| nfrle { x l A } : forall u, closed u -> nprove l (frl x A) -> nprove l (subs x u A)
with rprove : list formula -> formula -> Type := (* normal forms *)
| rninj { l A } : nprove l A -> rprove l A
| rimpi { l A B } : rprove (A :: l) B -> rprove l (imp A B)
| rfrli { x l A } : rprove (map fupz l) (subs x (dvar 0) (fupz A)) -> rprove l (frl x A)
| rexsi { x l A } : forall u, closed u -> rprove l (subs x u A) -> rprove l (exs x A)
| rexse { l C } : forall x A, nprove l (exs x A) ->
                              rprove (subs x (dvar 0) (fupz A) :: map fupz l) (fupz C) -> rprove l C.
Hint Constructors nprove rprove : term_db.

Scheme nrprove_rect := Induction for nprove Sort Type
  with rnprove_rect := Induction for rprove Sort Type.
Combined Scheme rnprove_mutrect from nrprove_rect, rnprove_rect.

Lemma nax_hd {l A} : nprove (A :: l) A.
Proof. rewrite <- (app_nil_l (A :: l)) ; apply nax. Qed.
Hint Resolve nax_hd : term_db.

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


(** substitutes [term] [u] for index [n] in normal form and decreases indexes above [n] *)
Theorem rnpsubs n u (Hc : closed u) {l A} :
   (nprove l A -> nprove (map (nsubs n u) l) (nsubs n u A))
 * (rprove l A -> rprove (map (nsubs n u) l) (nsubs n u A)).
Proof with try eassumption.
revert l A.
enough ((forall l A, nprove l A -> forall n u, closed u -> nprove (map (nsubs n u) l) (nsubs n u A))
      * (forall l A, rprove l A -> forall n u, closed u -> rprove (map (nsubs n u) l) (nsubs n u A)))
  as He by (split ; intros ; apply He ; assumption).
clear n u Hc ; apply rnprove_mutrect ; intros ; (try simpl in X) ;
  (try assert (IH1 := X n0 u H)) ; (try assert (IH2 := X0 n0 u H)) ; 
  (try (econstructor ; (eassumption + intuition) ; fail)).
- rewrite map_app ; apply nax.
- rnow idtac then rnow eapply nfrle.
- assert (closed (fup 0 u)) by rnow idtac.
  specialize X with (S n) (fup 0 u).
  rewrite map_map in X ; rewrite (map_ext _ _ (nsubs_fup_com _ _)) in X ; rewrite <- map_map in X.
  rnow autorewrite with term_db in X.
- rnow specialize X with n u0 then rnow eapply (rexsi (nsubs n u0 u)).
- rewrite <- (freevars_fup 0) in H.
  clear IH2 ; assert (IH2 := X0 (S n0) (fup 0 u) H) ; simpl in IH2.
  rewrite map_map in IH2 ; rewrite (map_ext _ _ (nsubs_fup_com _ _)) in IH2 ;
    rewrite <- map_map in IH2.
  rnow eapply rexse.
Qed.

Lemma rpsubsz_r {l A x u} : closed u ->
  rprove (map fupz l) (subs x (dvar 0) (fupz A)) -> rprove l (subs x u A).
Proof with try assumption.
intros Hc pi.
apply (rnpsubs 0 u) in pi...
rnow simpl in pi then simpl in pi.
rewrite map_map in pi ; rewrite (map_ext _ _ (nsubs_z_fup _)) in pi ; rewrite map_id in pi...
Qed.

Lemma rpsubsz_l {l A x u C} : closed u ->
  rprove (subs x (dvar 0) (fupz A) :: map fupz l) (fupz C) -> rprove (subs x u A :: l) C.
Proof with try assumption.
intros Hc pi.
apply (rnpsubs 0 u) in pi...
rnow simpl in pi then simpl in pi.
rewrite map_map in pi ; rewrite (map_ext _ _ (nsubs_z_fup _)) in pi ; rewrite map_id in pi...
Qed.


(** lift indexes above [k] in normal form *)
Theorem rnpup k {l A} :
   (nprove l A -> nprove (map (fup k) l) (fup k A))
 * (rprove l A -> rprove (map (fup k) l) (fup k A)).
Proof.
revert l A.
enough ((forall l A, nprove l A -> forall k, nprove (map (fup k) l) (fup k A))
      * (forall l A, rprove l A -> forall k, rprove (map (fup k) l) (fup k A)))
  as He by (split ; intros ; apply He ; assumption).
clear k ; apply rnprove_mutrect ; intros ; (try assert (IH1 := X k)) ; (try assert (IH2 := X0 k)) ;
  (try (econstructor ; eassumption ; fail)).
- rewrite map_app ; apply nax.
- rnow idtac then rnow apply nfrle.
- clear IH1 ; assert (IH := X (S k)).
  rnow change (dvar 0) with (fup (S k) (dvar 0)) in X.
  rewrite map_map in IH ; rewrite (map_ext _ _ (fup_fup_com _)) in IH ; rewrite <- map_map in IH.
  now apply rfrli.
- rnow idtac then rnow apply (rexsi (fup k u)).
- clear IH2 ; assert (IH2 := X0 (S k)) ; simpl in IH2.
  rnow change (dvar 0) with (tup (S k) (dvar 0)) in X.
  rewrite map_map in IH2 ; rewrite (map_ext _ _ (fup_fup_com _)) in IH2 ; rewrite <- map_map in IH2.
  rnow apply (rexse x (fup k A)).
Qed.

Theorem denormalization : (forall l A, nprove l A -> prove l A) * (forall l A, rprove l A -> prove l A).
Proof.
apply rnprove_mutrect ; intros ; try (econstructor ; eassumption) ; assumption.
Qed.

Lemma weakening :
   (forall l A, nprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> nprove (l1 ++ l0 ++ l2) A)
 * (forall l A, rprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> rprove (l1 ++ l0 ++ l2) A).
Proof.
apply rnprove_mutrect ; intros ; try (econstructor ; intuition ; intuition ; fail) ; subst.
- enough (forall l l3, l1 ++ A :: l2 = l3 ++ l4 -> nprove (l ++ l3 ++ l0 ++ l4) A)
    as HI by (rewrite <- (app_nil_l (l3 ++ l0 ++ l4)) ; apply HI ; assumption) ; clear.
  induction l1 ; intros l l3 Heq ; destruct l3 ; inversion Heq ; subst ; simpl.
  + simpl in H ; subst ; rewrite app_assoc ; apply nax.
  + apply nax.
  + simpl in H ; subst ; rewrite app_comm_cons ; rewrite 2 app_assoc ; apply nax.
  + replace (l ++ f :: l3 ++ l0 ++ l4) with ((l ++ f :: nil) ++ l3 ++ l0 ++ l4)
      by (rewrite <- app_assoc ; reflexivity).
    now apply IHl1.
- apply rimpi ; rewrite app_comm_cons ; intuition.
- apply rfrli ; rewrite ? map_app ; apply X ; rewrite map_app ; reflexivity.
- apply (rexse x A).
  + apply X ; reflexivity.
  + rewrite ? map_app ; rewrite app_comm_cons ; apply X0 ; rewrite map_app ; reflexivity.
Qed.

