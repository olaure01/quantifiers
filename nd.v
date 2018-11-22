Require Import PeanoNat.
Require Import Wf_nat.
Require Import Lia.
Require Import List.


(** * Different kinds of atoms *)

Parameter atom : Set.  (* propositional variables for [formula] *)
Parameter tatom : Set. (* function symbols for [term] *)
Parameter vatom : Set. (* variables for quantification *)
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


(** * Terms *)

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
(** [dvar] for De Bruijn style eigen variables in proofs *)
(** [tvar] for quantified variables in formulas *)
Inductive term : Set :=
| dvar : nat -> term
| tvar : vatom -> term
| tconstr : tatom -> list term -> term.

(** appropriate induction for [term] (with list inside): so called "nested fix" *)
Fixpoint term_ind_list_Forall t :
  forall P : term -> Prop,
  (forall n, P (dvar n)) ->
  (forall x, P (tvar x)) ->
  (forall f l, Forall P l -> P (tconstr f l)) -> P t :=
fun P Pdvar Ptvar Pconstr =>
match t with
| dvar n => Pdvar n
| tvar x => Ptvar x
| tconstr c l => Pconstr c l
    ((fix l_ind l' : Forall P l' :=
      match l' with
      | nil => Forall_nil P
      | cons t1 l1 => Forall_cons t1
                        (term_ind_list_Forall t1 P Pdvar Ptvar Pconstr)
                        (l_ind l1)
      end) l)
end.
Ltac term_induction t :=
  (try intros until t) ;
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  apply (term_ind_list_Forall t) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ;
    repeat (rewrite flat_map_concat_map) ; repeat (rewrite map_map) ;
    try f_equal ; try (apply map_ext_in ; apply Forall_forall) ;try assumption ].


(** lift indexes above [k] in [term] [t] *)
Fixpoint tup k t :=
match t with
| dvar n => if n <? k then dvar n else dvar (S n)
| tvar x => tvar x
| tconstr f l => tconstr f (map (tup k) l)
end.

Lemma tup_tup_com : forall k t,
  tup (S k) (tup 0 t) = tup 0 (tup k t).
Proof. term_induction t.
change (S n <? S k) with (n <? k) ; now case_eq (n <? k).
Qed.

(** * Term substitutions *)

(** substitutes [term] [u] for index [n] in [term] [v] and decreases indexes above [n] *)
Fixpoint ntsubs n u v :=
match v with
| tvar x => tvar x
| dvar k => match n ?= k with
            | Eq => u
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| tconstr f l => tconstr f (map (ntsubs n u) l)
end.

(** substitutes [term] [u] for variable [x] in [term] [t] *)
Fixpoint tsubs x u t :=
match t with
| tvar y => if (beq_vat y x) then u else tvar y
| dvar k => dvar k
| tconstr c l => tconstr c (map (tsubs x u) l)
end.

Lemma tup_tsubs_com : forall k x u t,
  tup k (tsubs x u t) = tsubs x (tup k u) (tup k t).
Proof. term_induction t.
- now case_eq (n <? k).
- now case_eq (beq_vat x0 x).
Qed.

Lemma ntsubs_tup_com : forall k u t,
  ntsubs (S k) (tup 0 u) (tup 0 t) = tup 0 (ntsubs k u t).
Proof. term_induction t.
case_eq (k ?= n) ; auto.
intros Heq ; destruct n ; auto.
exfalso ; destruct k ; inversion Heq.
Qed.

Lemma ntsubs_z_tup : forall u t, ntsubs 0 u (tup 0 t) = t.
Proof. term_induction t.
induction l ; auto.
inversion IHl ; subst ; simpl ; f_equal ; auto.
Qed.

Lemma ntsubs_z_tsubs_tup : forall u x t,
  ntsubs 0 u (tsubs x (dvar 0) (tup 0 t)) = tsubs x u t.
Proof. term_induction t.
now case_eq (beq_vat x0 x).
Qed.
Hint Resolve tup_tup_com tup_tsubs_com ntsubs_tup_com ntsubs_z_tup ntsubs_z_tsubs_tup.



(** ** Free variables *)

Fixpoint freevars t :=
match t with
| tvar X => X :: nil
| dvar _ => nil
| tconstr f l => flat_map freevars l
end.
Definition closed t := freevars t = nil.

Lemma freevars_tup : forall k t, freevars (tup k t) = freevars t.
Proof. term_induction t.
now case_eq (n <? k).
Qed.
Hint Rewrite freevars_tup.
Hint Resolve freevars_tup.

Lemma freevars_ntsubs : forall n u, closed u -> forall t,
  freevars (ntsubs n u t) = freevars t.
Proof. term_induction t.
now case_eq (n ?= n0).
Qed.

Lemma nfree_tsubs : forall x u t, ~ In x (freevars t) -> tsubs x u t = t.
Proof. term_induction t.
- case_eq (beq_vat x0 x) ; intuition.
  now apply vatomEq.eqb_eq in H.
- intros Hn ; f_equal ; revert IHl Hn ; induction l ; intros ; auto.
  inversion IHl0 ; subst.
  simpl in Hn ; simpl.
  rewrite H1 ; [ f_equal | ] ; intuition.
Qed.
Hint Rewrite freevars_ntsubs nfree_tsubs using assumption.

Lemma ntsubs_tsubs_com : forall x v n u, ~ In x (freevars u) -> forall t,
  ntsubs n u (tsubs x v t) = tsubs x (ntsubs n u v) (ntsubs n u t).
Proof. term_induction t.
- case_eq (n ?= n0) ; intros ; auto ; now autorewrite with core.
- now case_eq (beq_vat x0 x).
Qed.
Hint Rewrite ntsubs_tsubs_com using assumption.

Lemma ntsubs_tsubs_z_com : forall x n u t, ~ In x (freevars u) ->
  ntsubs (S n) u (tsubs x (dvar 0) t) = tsubs x (dvar 0) (ntsubs (S n) u t).
Proof. intros x n u t Hn. term_induction t.
- destruct n0 ; auto.
  case_eq (n ?= n0) ; auto.
  now rewrite nfree_tsubs.
- now (case_eq (beq_vat x0 x)).
Qed.
Hint Resolve ntsubs_tsubs_z_com.







(** * Formulas *)

(** formulas *)
(** first-order formulas in the langage: implication, universal quantification *)
Inductive formula : Set :=
| var : atom -> list term -> formula
| imp : formula -> formula -> formula
| frl : vatom -> formula -> formula.

Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let ll2 := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | A1 A2 | xx A ] ; simpl ;
  [ try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; intuition ;
                       rewrite IHll ; f_equal ; intuition)
  | try (f_equal ; intuition)
  | try (f_equal ; intuition) ].

(** size of formulas *)
Fixpoint fsize A :=
match A with
| var _ _ => 1
| imp B C => S (fsize B + fsize C)
| frl _ B => S (fsize B)
end.


(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X l => var X (map (tup k) l)
| imp B C => imp (fup k B) (fup k C)
| frl x B => frl x (fup k B)
end.

Lemma fsize_fup : forall k A, fsize (fup k A) = fsize A.
Proof. formula_induction A. Qed.

Lemma fup_fup_com : forall k A,
  fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof. formula_induction A. Qed.


(** substitutes [term] [u] for variable [x] in [formula] [A] *)
Fixpoint subs x u A :=
match A with
| var X l => var X (map (tsubs x u) l)
| imp B C => imp (subs x u B) (subs x u C)
| frl y B as C => if (beq_vat y x) then C else frl y (subs x u B)
end.

Lemma fsize_subs : forall u x A, fsize (subs x u A) = fsize A.
Proof.
formula_induction A.
case_eq (beq_vat x0 x) ; simpl ; auto.
Qed.

Lemma fup_subs_com : forall k x u A,
  fup k (subs x u A) = subs x (tup k u) (fup k A).
Proof. formula_induction A.
case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal ; auto.
Qed.

(** substitutes [term] [u] for index [n] in [formula] [A] *)
Fixpoint nsubs n u A :=
match A with
| var X l => var X (map (ntsubs n u) l)
| imp B C => imp (nsubs n u B) (nsubs n u C)
| frl x B as C => frl x (nsubs n u B)
end.

Lemma nsubs_fup_com : forall k u A,
  nsubs (S k) (tup 0 u) (fup 0 A) = fup 0 (nsubs k u A).
Proof. formula_induction A. Qed.

Lemma nsubs_z_fup : forall u A, nsubs 0 u (fup 0 A) = A.
Proof. formula_induction A. Qed.
Hint Resolve nsubs_z_fup.

Lemma nsubs_z_subs_fup : forall u x A,
  nsubs 0 u (subs x (dvar 0) (fup 0 A)) = subs x u A.
Proof. formula_induction A.
case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal ; auto.
Qed.

Lemma nsubs_subs_com : forall x v n u, closed u -> forall A,
  nsubs n u (subs x v A) = subs x (ntsubs n u v) (nsubs n u A).
Proof.
induction A ; simpl ; f_equal ; intuition.
- rewrite ? map_map ; apply map_ext ; intros t.
  rewrite ntsubs_tsubs_com ; auto.
  now rewrite H.
- case_eq (beq_vat v0 x) ; intros ; simpl ; f_equal ; auto.
Qed.

Lemma nsubs_subs_z_com : forall x n u, closed u -> forall A,
  nsubs (S n) u (subs x (dvar 0) A) = subs x (dvar 0) (nsubs (S n) u A).
Proof.
intros ; induction A ; simpl ; f_equal ; intuition.
- repeat rewrite map_map ; apply map_ext.
  intros ; rewrite ntsubs_tsubs_z_com ; auto.
  now rewrite H.
- case_eq (beq_vat v x) ; intros ; simpl ; f_equal ; auto.
Qed.
Hint Rewrite nsubs_subs_z_com using assumption.







(** * Proofs *)

(** Proofs *)
Inductive prove : list formula -> formula -> Set :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi { l A B } : prove (A :: l) B -> prove l (imp A B)
| impe { l B } : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli { x l A } : prove (map (fup 0) l) (subs x (dvar 0) (fup 0 A)) -> prove l (frl x A)
| frle { x l A } : forall u, closed u -> prove l (frl x A) -> prove l (subs x u A).


(** Normal Forms *)
Inductive nprove : list formula -> formula -> Set :=
| nax : forall l1 l2 A, nprove (l1 ++ A :: l2) A
| nimpe { l B } : forall A, nprove l (imp A B) -> rprove l A -> nprove l B
| nfrle { x l A } : forall u, closed u -> nprove l (frl x A) -> nprove l (subs x u A)
with rprove : list formula -> formula -> Set :=
| rninj { l A } : nprove l A -> rprove l A
| rimpi { l A B } : rprove (A :: l) B -> rprove l (imp A B)
| rfrli { x l A } : rprove (map (fup 0) l) (subs x (dvar 0) (fup 0 A)) -> rprove l (frl x A).

Scheme nrprove_rect := Induction for nprove Sort Type
  with rnprove_rect := Induction for rprove Sort Type.

(* to be automatically generated in more recent Coq versions with:
Combined Scheme rnprove_mutrect from nrprove_rect, rnprove_rect.
*)
Lemma rnprove_mutrect :
      forall (P : forall (l : list formula) (f : formula), nprove l f -> Type)
         (P0 : forall (l : list formula) (f : formula), rprove l f -> Type),
       (forall (l1 l2 : list formula) (A : formula), P (l1 ++ A :: l2) A (nax l1 l2 A)) ->
       (forall (l : list formula) (B A : formula) (n : nprove l (imp A B)),
        P l (imp A B) n -> forall r : rprove l A, P0 l A r -> P l B (nimpe A n r)) ->
       (forall (x : vatom) (l : list formula) (A : formula) (u : term) (e : closed u)
          (n : nprove l (frl x A)), P l (frl x A) n -> P l (subs x u A) (nfrle u e n)) ->
       (forall (l : list formula) (A : formula) (n : nprove l A), P l A n -> P0 l A (rninj n)) ->
       (forall (l : list formula) (A B : formula) (r : rprove (A :: l) B),
        P0 (A :: l) B r -> P0 l (imp A B) (rimpi r)) ->
       (forall (x : vatom) (l : list formula) (A : formula)
          (r : rprove (map (fup 0) l) (subs x (dvar 0) (fup 0 A))),
        P0 (map (fup 0) l) (subs x (dvar 0) (fup 0 A)) r -> P0 l (frl x A) (rfrli r)) ->
(*
       (forall (l : list formula) (f5 : formula) (n : nprove l f5), P l f5 n) *
       forall (l : list formula) (f5 : formula) (r : rprove l f5), P0 l f5 r.
*)
       forall (l : list formula) (f5 : formula),
         ((forall (n : nprove l f5), P l f5 n) * (forall (n : rprove l f5), P0 l f5 n)).
Proof.
intros ; split ; [ eapply nrprove_rect | eapply rnprove_rect ] ; eassumption.
Qed.

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
enough ((nprove l A -> forall n u, closed u -> nprove (map (nsubs n u) l) (nsubs n u A))
      * (rprove l A -> forall n u, closed u -> rprove (map (nsubs n u) l) (nsubs n u A)))
  as He by (split ; intros ; apply He ; assumption).
clear n u Hc ; revert l A ; apply rnprove_mutrect ;
  intros ; simpl in H ; (try assert (IH1 := H n0 u H1)) ; (try assert (IH2 := H0 n0 u H1)) ; 
  (try (econstructor ; (eassumption + intuition) ; fail)).
- rewrite map_app ; apply nax.
- rewrite nsubs_subs_com...
  eapply nfrle ; intuition.
  unfold closed ; rewrite freevars_ntsubs...
- unfold closed in H0 ; rewrite <- (freevars_tup 0) in H0.
  specialize H with (S n) (tup 0 u).
  rewrite nsubs_subs_z_com in H...
  rewrite nsubs_fup_com in H.
  rewrite map_map in H ; rewrite (map_ext _ _ (nsubs_fup_com _ _)) in H ; rewrite <- map_map in H.
  apply rfrli ; intuition.
Qed.

(** lift indexes above [k] in normal form *)
Theorem rnpup k {l A} :
   (nprove l A -> nprove (map (fup k) l) (fup k A))
 * (rprove l A -> rprove (map (fup k) l) (fup k A)).
Proof with try eassumption.
enough ((nprove l A -> forall k, nprove (map (fup k) l) (fup k A))
      * (rprove l A -> forall k, rprove (map (fup k) l) (fup k A)))
  as He by (split ; intros ; apply He ; assumption).
clear k ; revert l A ; apply rnprove_mutrect ;
  intros ; (try assert (IH1 := H k)) ; (try assert (IH2 := H0 k)) ;
  (try (econstructor ; eassumption ; fail)).
- rewrite map_app ; apply nax.
- rewrite fup_subs_com.
  apply nfrle...
  unfold closed ; rewrite freevars_tup...
- clear IH1 ; assert (IH := H (S k)).
  change (dvar 0) with (tup (S k) (dvar 0)) in H.
  rewrite fup_subs_com in IH.
  rewrite fup_fup_com in IH.
  rewrite map_map in IH ; rewrite (map_ext _ _ (fup_fup_com _)) in IH ; rewrite <- map_map in IH.
  apply rfrli...
Qed.





(** * Normalization *)

Theorem denormalization {l A} : (nprove l A -> prove l A) * (rprove l A -> prove l A).
Proof.
revert l A ; apply rnprove_mutrect ; intros ; try (econstructor ; eassumption) ; assumption.
Qed.

Lemma weakening : forall l A,
   (nprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> nprove (l1 ++ l0 ++ l2) A)
 * (rprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> rprove (l1 ++ l0 ++ l2) A).
Proof.
apply rnprove_mutrect ; intros ; try (econstructor ; intuition ; fail) ; subst.
- enough (forall l l3, l1 ++ A :: l2 = l3 ++ l4 -> nprove (l ++ l3 ++ l0 ++ l4) A)
    as HI by (rewrite <- (app_nil_l (l3 ++ l0 ++ l4)) ; apply HI ; assumption) ; clear.
  induction l1 ; intros l l3 Heq ; destruct l3 ; inversion Heq ; subst ; simpl.
  + simpl in H ; subst.
    rewrite app_assoc ; apply nax.
  + apply nax.
  + simpl in H ; subst.
    rewrite app_comm_cons ; rewrite 2 app_assoc ; apply nax.
  + replace (l ++ f :: l3 ++ l0 ++ l4) with ((l ++ f :: nil) ++ l3 ++ l0 ++ l4)
      by (rewrite <- app_assoc ; reflexivity).
    apply IHl1 ; assumption.
- apply rimpi ; rewrite app_comm_cons ; intuition.
- apply rfrli ; rewrite ? map_app ; apply H ; rewrite map_app ; reflexivity.
Qed.

Lemma substitution : forall n m l A, fsize A = n -> rprove l A ->
   (forall B l0 l1 l2 (pi : nprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
      nsize pi < m -> fsize A < fsize B -> nprove (l1 ++ l2) B)
 * (forall B l0 l1 l2 (pi : nprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
      nsize pi < m -> rprove (l1 ++ l2) B)
 * (forall B l0 l1 l2 (pi : rprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
     rsize pi < m -> rprove (l1 ++ l2) B).
Proof with try eassumption ; try reflexivity ; try lia.
apply (lt_wf_double_rec (fun n m => 
 forall l A, fsize A = n -> rprove l A ->
   (forall B l0 l1 l2 (pi : nprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
      nsize pi < m -> fsize A < fsize B -> nprove (l1 ++ l2) B)
 * (forall B l0 l1 l2 (pi : nprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
      nsize pi < m -> rprove (l1 ++ l2) B)
 * (forall B l0 l1 l2 (pi : rprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
      rsize pi < m -> rprove (l1 ++ l2) B))) ;
  intros n m IHn IHm l A HA pi1 ; (split ; [ split | ] ) ; subst ;
  intros B l0 l1 l2 pi2 Hl Hpi ; [ intros HF | | ] ;
  remember (l1 ++ A :: l2) as ll ; destruct pi2 ; subst ;
  simpl in IHm ; simpl in IHn ; simpl in Hpi ; try simpl in HF.
- clear - Heqll HF ; revert l1 l2 Heqll HF ; induction l3 ; intros l1 l2 Heqll HF ;
    destruct l1 ; inversion Heqll ; subst.
  + exfalso...
  + simpl ; rewrite <- (app_nil_l (f :: _)).
    apply nax.
  + apply nax.
  + apply IHl3 in H1...
    change (f :: l1) with (nil ++ (f :: nil) ++ l1) ; rewrite <- ? app_assoc.
    eapply weakening...
- apply (IHm (S (nsize pi2 + rsize r))) in pi1...
  assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  eapply nimpe ; eapply pi1 ; simpl...
- apply (IHm _ Hpi) in pi1...
  apply nfrle...
  rewrite fsize_subs in HF.
  eapply (fst (fst pi1) _ _ _ _ pi2) ; simpl...
- enough (forall ll l l0 l1,
    rprove l A -> l0 ++ l = ll ++ l1 ++ l2 -> l3 ++ A0 :: l4 = l1 ++ A :: l2 ->
      rprove (ll ++ l1 ++ l2) A0)
    as HI by (eapply (HI nil) ; eassumption) ; clear.
  induction l3 ; intros ll l l0 l1 pi1 Hl Heqll ; destruct l1 ; inversion Heqll ; subst.
  + rewrite <- Hl.
    rewrite <- (app_nil_l (l0 ++ l)).
    eapply weakening...
  + simpl ; rewrite <- (app_nil_l (f :: _)).
    apply rninj ; apply nax.
  + rewrite ? app_assoc ; apply rninj ; apply nax.
  + destruct l0 ; inversion Hl ; simpl in Hl ; subst.
    * eapply (IHl3 (ll ++ f :: nil) _ nil l1) in pi1...
      -- rewrite <- ? app_assoc in pi1...
      -- rewrite <- ? app_assoc...
    * eapply (IHl3 _ _ (f0 :: l0)) in H1...
      -- replace (ll ++ (f :: l1) ++ l2) with ((ll ++ f :: nil) ++ l1 ++ l2)...
         rewrite <- ? app_assoc...
      -- simpl ; rewrite Hl ; rewrite <- ? app_assoc...
- apply (IHm (S (nsize pi2 + rsize r))) in pi1...
  assert (nsize pi2 < S (nsize pi2 + rsize r)) as IH1 by lia.
  assert (rsize r < S (nsize pi2 + rsize r)) as IH2 by lia.
  destruct (Compare_dec.le_lt_dec (fsize (imp A0 B)) (fsize A)).
  + eapply pi1 in IH1 ; eapply pi1 in IH2...
    inversion IH1 ; subst.
    * apply rninj ; eapply nimpe ; simpl...
    * remember (rsize H1) as q.
      eapply (IHn _ (S q)) in IH2 ; [ | simpl in l3 | reflexivity ]...
      revert H1 Heqq ; rewrite <- (app_nil_l (A0 :: _)) ; intros H1 Heqq.
      refine (snd IH2 _ _ _ _ H1 eq_refl _)...
  + apply rninj ; eapply nimpe ; eapply pi1 ; simpl...
- apply (IHm (S (nsize pi2))) in pi1...
  assert (nsize pi2 < S (nsize pi2)) as IH1 by lia.
  destruct (Compare_dec.le_lt_dec (fsize (frl x A0)) (fsize A)).
  + eapply pi1 in IH1...
    inversion IH1 ; subst.
    * apply rninj ; eapply nfrle ; simpl...
    * apply (rnpsubs 0 u) in H1...
      rewrite map_map in H1.
      rewrite (map_ext _ _ (nsubs_z_fup _)) in H1.
      rewrite map_id in H1.
      rewrite nsubs_z_subs_fup in H1...
  + apply rninj ; eapply nfrle...
    eapply pi1...
- refine (snd (fst (IHm _ Hpi _ _ _ pi1)) _ _ _ _ n _ _)...
- revert pi2 Hpi ; rewrite app_comm_cons ; intros pi2 Hpi.
  apply rimpi.
  refine (snd (IHm _ Hpi _ _ _ pi1) _ _ _ _ pi2 _ _)...
  simpl ; rewrite <- Hl ; rewrite app_comm_cons ; reflexivity.
- apply rfrli.
  revert pi2 Hpi ; rewrite map_app ; simpl ; intros pi2 Hpi.
  apply (rnpup 0) in pi1.
  rewrite map_app.
  refine (snd (IHm _ Hpi _ _ _ pi1) _ _ _ _ pi2 _ _)...
  + rewrite fsize_fup...
  + rewrite <- ? map_app ; f_equal ; rewrite <- Hl...
Qed.

Lemma smp_substitution : forall l A B, rprove l A -> rprove (A :: l) B -> rprove l B.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A B pi1 pi2.
eapply (substitution _ (S (rsize pi2))) in pi1...
rewrite <- (app_nil_l l).
revert pi2 pi1 ; rewrite <- (app_nil_l (A :: l)) ; intros pi2 pi1.
refine (snd pi1 _ _ _ _ pi2 _ _)...
Qed.


Theorem normalization : forall l A, prove l A -> rprove l A.
Proof with try eassumption.
intros l A pi ; induction pi ;
  try (constructor ; assumption) ;
  try (do 2 constructor ; assumption).
- inversion IHpi1 ; subst.
  + apply rninj ; eapply nimpe...
  + eapply smp_substitution...
- inversion IHpi ; subst.
  + apply rninj ; eapply nfrle...
  + apply (rnpsubs 0 u) in H1...
    rewrite map_map in H1.
    rewrite (map_ext _ _ (nsubs_z_fup _)) in H1.
    rewrite map_id in H1.
    rewrite nsubs_z_subs_fup in H1...
Qed.



(** * Free variables in [formula] *)
Fixpoint ffreevars A :=
match A with
| var _ l => fold_right (fun x s => app (freevars x) s)  nil l
| imp B C => (ffreevars B) ++ (ffreevars C)
| frl x B => remove vatomEq.eq_dec x (ffreevars B)
end.

Lemma in_ffreevars_frl : forall x y, beq_vat y x = false -> forall A,
  In x (ffreevars A) -> In x (ffreevars (frl y A)).
Proof.
intros x y Heq A Hi ; simpl ; remember (ffreevars A) as l.
revert Hi ; clear - Heq ; induction l ; intros Hi ; auto.
inversion Hi ; subst ; simpl.
- destruct (vatomEq.eq_dec y x) ; intuition ; subst.
  rewrite eqb_refl in Heq ; inversion Heq.
- destruct (vatomEq.eq_dec y a) ; intuition.
Qed.

Lemma ffreevars_fup : forall k A, ffreevars (fup k A) = ffreevars A.
Proof.
intros k A ; revert k ; formula_induction A.
- f_equal ; intuition.
- rewrite IHA ; reflexivity.
Qed.

Lemma nfree_subs : forall x u A, ~ In x (ffreevars A) -> subs x u A = A.
Proof.
induction A ; simpl ; intuition ; f_equal ; intuition.
- induction l ; intuition.
  simpl ; f_equal.
  + apply nfree_tsubs.
    intros Hf ; apply H ; simpl ; intuition.
  + apply IHl ; intros Hf ; apply H ; simpl ; intuition.
- case_eq (beq_vat v x) ; intuition.
  f_equal ; apply IHA.
  intros Hf ; apply H ; apply in_ffreevars_frl ; assumption.
Qed.



(** * Hilbert style properties *)

(* Apply all (reversible) introduction rules *)
Ltac rev_intros := repeat (repeat apply rimpi ; repeat apply rfrli) ; apply rninj.

Lemma frl_elim : forall A u x, closed u -> rprove (frl x A :: nil) (subs x u A).
Proof.
intros A u x Hf ; rev_intros.
apply (nfrle u) ; [ assumption | ].
rewrite <- (app_nil_l (frl x A :: nil)).
apply nax.
Qed.

Lemma frl_imp : forall A B x, rprove (frl x (imp A B) :: nil) (imp (frl x A) (frl x B)).
Proof.
intros A B x ; rev_intros.
apply (nimpe (subs x (dvar 0) (fup 0 A))).
- change (imp (subs x (dvar 0) (fup 0 A)) (subs x (dvar 0) (fup 0 B)))
    with (subs x (dvar 0) (imp (fup 0 A) (fup 0 B))).
  apply nfrle ; [ reflexivity | ].
  change (frl x (imp (fup 0 A) (fup 0 B)))
    with (fup 0 (frl x (imp A B))).
  apply rnpup.
  change (frl x A :: frl x (imp A B) :: nil)
    with ((frl x A :: nil) ++ frl x (imp A B) :: nil).
  apply nax.
- apply rninj ; apply nfrle ; [ reflexivity | ].
  simpl ; rewrite <- (app_nil_l (frl x _ :: _)).
  apply nax.
Qed.

Lemma frl_nfree : forall A x, ~ In x (ffreevars A) -> rprove (A :: nil) (frl x A).
Proof.
intros A x Hnf ; rev_intros.
rewrite nfree_subs.
- simpl ; rewrite <- (app_nil_l (fup 0 A :: nil)).
  apply nax.
- now rewrite ffreevars_fup.
Qed.

Lemma Kcombi : forall A B, rprove nil (imp A (imp B A)).
Proof.
intros ; rev_intros.
change (B :: A :: nil) with ((B :: nil) ++ A :: nil).
apply nax.
Qed.

Lemma Scombi : forall A B C, rprove nil (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).
Proof.
intros ; rev_intros.
apply (nimpe B).
- apply (nimpe A).
  + change (A :: imp A B :: imp A (imp B C) :: nil)
      with ((A :: imp A B :: nil) ++ imp A (imp B C) :: nil).
    apply nax.
  + rewrite <- (app_nil_l (A :: _)).
    apply rninj ; apply nax.
- apply rninj ; apply (nimpe A).
  + change (A :: imp A B :: imp A (imp B C) :: nil)
      with ((A :: nil) ++ imp A B :: imp A (imp B C) :: nil).
    apply nax.
  + rewrite <- (app_nil_l (A :: _)).
    apply rninj ; apply nax.
Qed.




