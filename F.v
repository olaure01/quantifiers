(* Natural Deduction for Second-Order Propositional Intuitionistic Logic *)
(*  aka System F *)

Require Import PeanoNat Lia.
Require Import List_more dectype Wf_nat_more.
Require Import term_tactics.

Hint Resolve in_in_remove : term_db.

Parameter atom : Type. (* second-order constants *)
Parameter vatom : DecType. (* variables for quantification *)


(** * Formulas *)

(** formulas *)
(** second-order formulas *)
Inductive formula :=
| var : vatom -> formula
| dvar : nat -> formula
| cst : atom -> formula
| imp : formula -> formula -> formula
| frl : vatom -> formula -> formula.

Ltac formula_induction A :=
  (try intros until A) ;
  let X := fresh "X" in
  let K := fresh "k" in
  let P := fresh "P" in
  let A1 := fresh A in
  let A2 := fresh A in
  let Y := fresh "X" in
  induction A as [ X | K | P | A1 A2 | Y A ] ; simpl ; intros ;
    try (f_equal ; intuition) ; try ((rnow idtac) ; fail) ; try (rcauto ; fail).


(** size of formulas *)
Fixpoint fsize A :=
match A with
| var _ => 1
| dvar _ => 1
| cst _ => 1
| imp B C => S (fsize B + fsize C)
| frl _ B => S (fsize B)
end.


(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X => var X
| dvar n => if n <? k then dvar n else dvar (S n)
| cst R => cst R
| imp B C => imp (fup k B) (fup k C)
| frl X B => frl X (fup k B)
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
| var Y => if (eqb Y X) then F else var Y
| cst R => cst R
| imp B C => imp (subs X F B) (subs X F C)
| frl Y B => frl Y (if (eqb Y X) then B else subs X F B)
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
| frl X B => remove eq_dt_dec X (freevars B)
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
Proof. formula_induction A. Qed.
Hint Rewrite nfree_subs using try (intuition ; fail) ;
                              (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma nsubs_subs_com : forall X F n G, ~ In X (freevars G) -> forall A,
  nsubs n G (subs X F A) = subs X (nsubs n G F) (nsubs n G A).
Proof. formula_induction A. Qed.
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
| frle { X l A } : forall C, closed C -> prove l (frl X A) -> prove l (subs X C A).
Hint Constructors prove : term_db.

(** Normal Forms *)
Inductive nprove : list formula -> formula -> Type := (* neutral terms *)
| nax : forall l1 l2 A, nprove (l1 ++ A :: l2) A
| nimpe { l B } : forall A, nprove l (imp A B) -> rprove l A -> nprove l B
| nfrle { x l A } : forall u, closed u -> nprove l (frl x A) -> nprove l (subs x u A)
with rprove : list formula -> formula -> Type := (* normal forms *)
| rninj { l A } : nprove l A -> rprove l A
| rimpi { l A B } : rprove (A :: l) B -> rprove l (imp A B)
| rfrli { x l A } : rprove (map fupz l) (subs x (dvar 0) (fupz A)) -> rprove l (frl x A).
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
clear k ; apply rnprove_mutrect ; intros ;
  (try assert (IH1 := X k)) ; (try assert (IH2 := X0 k)) ;
  (try (econstructor ; eassumption ; fail)).
- rewrite map_app ; apply nax.
- rnow idtac then rnow apply nfrle.
- clear IH1 ; assert (IH := X (S k)).
  rnow change (dvar 0) with (fup (S k) (dvar 0)) in X.
  rewrite map_map in IH ; rewrite (map_ext _ _ (fup_fup_com _)) in IH ; rewrite <- map_map in IH.
  now apply rfrli.
Qed.

Theorem denormalization :
   (forall l A, nprove l A -> prove l A)
 * (forall l A, rprove l A -> prove l A).
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
Qed.


Lemma imp_reduction : forall A B l, rprove l (imp A B) ->
(forall D l B, fsize D = fsize A -> rprove (D :: l) B -> rprove l D -> rprove l B) -> 
  rprove l A -> rprove l B.
Proof with try eassumption ; try reflexivity.
intros A B l pi.
remember (imp A B) as C ; revert A B HeqC ; induction pi ;
  intros A1 B1 HeqC ; inversion HeqC ; subst ; intros Hsub pi2.
- apply rninj ; eapply nimpe...
- eapply Hsub...
Qed.

Lemma frl_reduction : forall A x l, rprove l (frl x A) ->
  forall u, closed u -> rprove l (subs x u A).
Proof with try eassumption ; try reflexivity.
intros A x l pi.
remember (frl x A) as C ; revert A x HeqC ; induction pi ;
  intros A1 x1 HeqC ; inversion HeqC ; subst ; intros u Hc.
- apply rninj ; eapply nfrle...
- eapply rpsubsz_r in pi...
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
- clear - Heqll HF ; revert l1 l2 Heqll HF ; induction l0 ; intros l1 l2 Heqll HF ;
    destruct l1 ; inversion Heqll ; subst.
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
  etransitivity...
admit.
(* second statement *)
- enough (forall l l1 l2, l0 ++ A0 :: l3 = l1 ++ A :: l2 ->
      rprove (l ++ l1 ++ l2) A -> rprove (l ++ l1 ++ l2) A0)
    as HI by (eapply (HI nil) ; eassumption) ; clear.
  induction l0 ; intros l l1 l2 Heq pi ; destruct l1 ; inversion Heq ; subst...
  + rewrite <- app_comm_cons ; apply rninj ; apply nax.
  + rewrite 2 app_assoc ; apply rninj ; apply nax.
  + rewrite <- app_comm_cons ; rewrite <- (app_nil_l l1) ;
      rewrite <- app_assoc ; rewrite app_comm_cons ; rewrite app_assoc.
    apply IHl0...
    rewrite <- ? app_assoc ; rewrite <- app_comm_cons...
- assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  assert ({fsize (imp A0 B) <= fsize A} + {fsize A < fsize (imp A0 B)}) as [ Ho | Ho ]
    by (case (CompareSpec2Type (Nat.compare_spec (fsize (imp A0 B)) (fsize A))); intros Ho;
          [ left | left | right ]; lia).
  + eapply IHm in IH1 ; eapply IHm in IH2...
    eapply imp_reduction...
    simpl in Ho; intros D l' B' Heq pi1' pi2'.
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
  apply (rnpup 0) in pi1.
  revert pi1 pi2 Hpi ; rewrite ? map_app ; simpl ; intros pi1 pi2 Hpi.
  rnow refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _)...
Admitted.

Lemma smp_substitution : forall l A B, rprove l A -> rprove (A :: l) B -> rprove l B.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A B pi1 pi2.
rewrite <- (app_nil_l (A :: l)) in pi2 ; rewrite <- (app_nil_l l).
refine (snd (substitution _ (S (rsize pi2)) _ _ ) _ _ _ pi2 _ _)...
Qed.

Theorem normalization : forall l A, prove l A -> rprove l A.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A pi ; induction pi ;
   try (econstructor ; (idtac + econstructor) ; eassumption).
- eapply imp_reduction...
  clear ; intros ; eapply smp_substitution...
- eapply frl_reduction...
Qed.

