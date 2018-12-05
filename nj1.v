Require Import PeanoNat.
Require Import Wf_nat.
Require Import Lia.
Require Import List.

Tactic Notation "rnow" tactic(t) :=
  t ; simpl ; autorewrite with core in * ; simpl ; intuition.
Tactic Notation "rnow" tactic(t) "then" tactic(t1) :=
  t ; simpl ; autorewrite with core in * ; simpl ; intuition t1 ; simpl ; intuition.

Lemma ltb_S : forall n m, (S n <? S m) = (n <? m).
Proof. reflexivity. Qed.
Hint Rewrite ltb_S.

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

Ltac case_analysis :=
match goal with
| |- context f [?x =? ?y] => case_eq (x =? y)
| |- context f [?x <? ?y] => case_eq (x <? y)
| |- context f [?x ?= ?y] => case_eq (x ?= y)
| |- context f [beq_vat ?x ?y] => case_eq (beq_vat x y)
| |- context f [vatomEq.eq_dec ?x  ?y] => case_eq (vatomEq.eq_dec x y)
end.
Ltac rcauto := simpl ; autorewrite with core in * ; simpl ; rnow case_analysis.



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
    try f_equal ; try (apply map_ext_in ; apply Forall_forall) ; try assumption ] ;
  try ((rnow idtac) ; fail).


(** lift indexes above [k] in [term] [t] *)
Fixpoint tup k t :=
match t with
| dvar n => if n <? k then dvar n else dvar (S n)
| tvar x => tvar x
| tconstr f l => tconstr f (map (tup k) l)
end.

Lemma tup_tup_com : forall k t,
  tup (S k) (tup 0 t) = tup 0 (tup k t).
Proof. term_induction t ; rcauto. Qed.
Hint Rewrite tup_tup_com.

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
Proof. term_induction t ; rcauto. Qed.
Hint Rewrite tup_tsubs_com.

Lemma ntsubs_tup_com : forall k u t,
  ntsubs (S k) (tup 0 u) (tup 0 t) = tup 0 (ntsubs k u t).
Proof. term_induction t ; rcauto.
now destruct n ; destruct k ; inversion H.
Qed.
Hint Rewrite ntsubs_tup_com.

Lemma ntsubs_z_tup : forall u t, ntsubs 0 u (tup 0 t) = t.
Proof. term_induction t.
now rewrite <- (map_id l) at 2 ; apply map_ext_in ; apply Forall_forall.
Qed.
Hint Rewrite ntsubs_z_tup.



(** ** Free variables *)

Fixpoint freevars t :=
match t with
| tvar x => x :: nil
| dvar _ => nil
| tconstr f l => flat_map freevars l
end.
Notation closed t := (freevars t = nil).

Lemma closed_nofreevars : forall t x, closed t -> ~ In x (freevars t).
Proof. intros t X Hc Hin ; now rewrite Hc in Hin. Qed.

Lemma freevars_tup : forall k t, freevars (tup k t) = freevars t.
Proof. term_induction t ; rcauto. Qed.
Hint Rewrite freevars_tup.

Lemma freevars_ntsubs : forall n u, closed u -> forall t,
  freevars (ntsubs n u t) = freevars t.
Proof. term_induction t ; rcauto. Qed.
Hint Rewrite freevars_ntsubs using intuition ; fail.

Lemma nfree_tsubs : forall x u t, ~ In x (freevars t) -> tsubs x u t = t.
Proof. term_induction t ; try rcauto.
- now apply vatomEq.eqb_eq in H.
- rnow intros Heq ; f_equal ; revert IHl Heq ; induction l ; intros.
  rnow inversion IHl0 ; subst ; rewrite H1 ; [ f_equal | ] ; simpl in Heq.
Qed.
Hint Rewrite nfree_tsubs using try (intuition ; fail) ;
                               (try apply closed_nofreevars) ; intuition ; fail.

Lemma ntsubs_tsubs_com : forall x v n u, ~ In x (freevars u) -> forall t,
  ntsubs n u (tsubs x v t) = tsubs x (ntsubs n u v) (ntsubs n u t).
Proof. term_induction t ; rcauto. Qed.
Hint Rewrite ntsubs_tsubs_com using try (intuition ; fail) ;
                                    (try apply closed_nofreevars) ; intuition ; fail.



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
  induction A as [ XX ll | A1 A2 | xx A ] ; simpl ; intros ;
  [ try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; intuition ;
                       rewrite IHll ; f_equal ; intuition)
  | try (f_equal ; intuition)
  | try (f_equal ; intuition) ] ; try ((rnow idtac) ; fail).

(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X l => var X (map (tup k) l)
| imp B C => imp (fup k B) (fup k C)
| frl x B => frl x (fup k B)
end.

Lemma fup_fup_com : forall k A,
  fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof. formula_induction A. Qed.
Hint Rewrite fup_fup_com.


(** substitutes [term] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint subs x u A :=
match A with
| var X l => var X (map (tsubs x u) l)
| imp B C => imp (subs x u B) (subs x u C)
| frl y B as C => if (beq_vat y x) then C else frl y (subs x u B)
end.

Lemma fup_subs_com : forall k x u A,
  fup k (subs x u A) = subs x (tup k u) (fup k A).
Proof. formula_induction A.
rnow case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal.
Qed.
Hint Rewrite fup_subs_com.

(** substitutes [term] [u] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint nsubs n u A :=
match A with
| var X l => var X (map (ntsubs n u) l)
| imp B C => imp (nsubs n u B) (nsubs n u C)
| frl x B => frl x (nsubs n u B)
end.

Lemma nsubs_fup_com : forall k u A,
  nsubs (S k) (tup 0 u) (fup 0 A) = fup 0 (nsubs k u A).
Proof. formula_induction A. Qed.
Hint Rewrite nsubs_fup_com.

Lemma nsubs_z_fup : forall u A, nsubs 0 u (fup 0 A) = A.
Proof. formula_induction A. Qed.
Hint Rewrite nsubs_z_fup.

Lemma nsubs_subs_com : forall x v n u, ~ In x (freevars u) -> forall A,
  nsubs n u (subs x v A) = subs x (ntsubs n u v) (nsubs n u A).
Proof. now formula_induction A ; rcauto ; f_equal. Qed.
Hint Rewrite nsubs_subs_com using try (intuition ; fail) ;
                                  (try apply closed_nofreevars) ; intuition ; fail.


(** size of formulas *)
Fixpoint fsize A :=
match A with
| var _ _ => 1
| imp B C => S (fsize B + fsize C)
| frl _ B => S (fsize B)
end.

Lemma fsize_fup : forall k A, fsize (fup k A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_fup.

Lemma fsize_subs : forall u x A, fsize (subs x u A) = fsize A.
Proof. formula_induction A ; rcauto. Qed.
Hint Rewrite fsize_subs.




(** * Proofs *)

Notation fupz := (fup 0).

(** Proofs *)
Inductive prove : list formula -> formula -> Set :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi { l A B } : prove (A :: l) B -> prove l (imp A B)
| impe { l B } : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli { x l A } : prove (map fupz l) (subs x (dvar 0) (fupz A)) -> prove l (frl x A)
| frle { x l A } : forall u, closed u -> prove l (frl x A) -> prove l (subs x u A).


(** Normal Forms *)
Inductive nprove : list formula -> formula -> Set :=
| nax : forall l1 l2 A, nprove (l1 ++ A :: l2) A
| nimpe { l B } : forall A, nprove l (imp A B) -> rprove l A -> nprove l B
| nfrle { x l A } : forall u, closed u -> nprove l (frl x A) -> nprove l (subs x u A)
with rprove : list formula -> formula -> Set :=
| rninj { l A } : nprove l A -> rprove l A
| rimpi { l A B } : rprove (A :: l) B -> rprove l (imp A B)
| rfrli { x l A } : rprove (map fupz l) (subs x (dvar 0) (fupz A)) -> rprove l (frl x A).

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
          (r : rprove (map fupz l) (subs x (dvar 0) (fupz A))),
        P0 (map fupz l) (subs x (dvar 0) (fupz A)) r -> P0 l (frl x A) (rfrli r)) ->
(*
       (forall (l : list formula) (f5 : formula) (n : nprove l f5), P l f5 n) *
       forall (l : list formula) (f5 : formula) (r : rprove l f5), P0 l f5 r.
*)
       forall (l : list formula) (f5 : formula),
         ((forall (n : nprove l f5), P l f5 n) * (forall (n : rprove l f5), P0 l f5 n)).
Proof.
intros ; split ; [ eapply nrprove_rect | eapply rnprove_rect ] ; eassumption.
Qed.

Lemma nax_hd {l A} : nprove (A :: l) A.
Proof. rewrite <- (app_nil_l (A :: l)) ; apply nax. Qed.

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
- rnow idtac then rnow eapply nfrle.
- assert (closed (tup 0 u)) by rnow idtac.
  specialize H with (S n) (tup 0 u). 
  rewrite map_map in H ; rewrite (map_ext _ _ (nsubs_fup_com _ _)) in H ; rewrite <- map_map in H.
  rnow autorewrite with core in H ; apply rfrli.
Qed.

(** lift indexes above [k] in normal form *)
Theorem rnpup k {l A} :
   (nprove l A -> nprove (map (fup k) l) (fup k A))
 * (rprove l A -> rprove (map (fup k) l) (fup k A)).
Proof.
enough ((nprove l A -> forall k, nprove (map (fup k) l) (fup k A))
      * (rprove l A -> forall k, rprove (map (fup k) l) (fup k A)))
  as He by (split ; intros ; apply He ; assumption).
clear k ; revert l A ; apply rnprove_mutrect ;
  intros ; (try assert (IH1 := H k)) ; (try assert (IH2 := H0 k)) ;
  (try (econstructor ; eassumption ; fail)).
- rewrite map_app ; apply nax.
- rnow idtac then rnow apply nfrle.
- clear IH1 ; assert (IH := H (S k)).
  rnow change (dvar 0) with (tup (S k) (dvar 0)) in H.
  rewrite map_map in IH ; rewrite (map_ext _ _ (fup_fup_com _)) in IH ; rewrite <- map_map in IH.
  now apply rfrli.
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
  + simpl in H ; subst ; rewrite app_assoc ; apply nax.
  + apply nax.
  + simpl in H ; subst ; rewrite app_comm_cons ; rewrite 2 app_assoc ; apply nax.
  + replace (l ++ f :: l3 ++ l0 ++ l4) with ((l ++ f :: nil) ++ l3 ++ l0 ++ l4)
      by (rewrite <- app_assoc ; reflexivity).
    now apply IHl1.
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
  + apply nax_hd.
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
  rnow eapply (fst (fst pi1) _ _ _ _ pi2)...
- enough (forall ll l l0 l1,
    rprove l A -> l0 ++ l = ll ++ l1 ++ l2 -> l3 ++ A0 :: l4 = l1 ++ A :: l2 ->
      rprove (ll ++ l1 ++ l2) A0)
    as HI by (eapply (HI nil) ; eassumption) ; clear.
  induction l3 ; intros ll l l0 l1 pi1 Hl Heqll ; destruct l1 ; inversion Heqll ; subst.
  + rewrite <- Hl ; rewrite <- (app_nil_l (l0 ++ l)) ; eapply weakening...
  + apply rninj ; apply nax.
  + rewrite ? app_assoc ; apply rninj ; apply nax.
  + destruct l0 ; inversion Hl ; simpl in Hl ; subst.
    * eapply (IHl3 (ll ++ f :: nil) _ nil l1) in pi1 ; rewrite_all <- app_assoc...
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
      rnow rewrite map_map in H1 ; rewrite (map_ext _ _ (nsubs_z_fup _)) in H1 ;
           rewrite map_id in H1.
  + apply rninj ; eapply nfrle...
    eapply pi1...
- refine (snd (fst (IHm _ Hpi _ _ _ pi1)) _ _ _ _ n _ _)...
- revert pi2 Hpi ; rewrite app_comm_cons ; intros pi2 Hpi.
  apply rimpi.
  refine (snd (IHm _ Hpi _ _ _ pi1) _ _ _ _ pi2 _ _)...
  simpl ; rewrite <- Hl ; rewrite app_comm_cons ; reflexivity.
- apply rfrli.
  apply (rnpup 0) in pi1.
  revert pi2 Hpi ; rewrite map_app ; simpl ; intros pi2 Hpi.
  rewrite map_app.
  rnow refine (snd (IHm _ Hpi _ _ _ pi1) _ _ _ _ pi2 _ _)...
  rewrite <- ? map_app ; f_equal ; rewrite <- Hl...
Qed.

Lemma smp_substitution : forall l A B, rprove l A -> rprove (A :: l) B -> rprove l B.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A B pi1 pi2.
rewrite <- (app_nil_l (A :: l)) in pi2 ; rewrite <- (app_nil_l l).
refine (snd (substitution _ (S (rsize pi2)) _ _ _ pi1) _ _ _ _ pi2 _ _)...
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
    rnow rewrite map_map in H1 ; rewrite (map_ext _ _ (nsubs_z_fup _)) in H1 ;
         rewrite map_id in H1.
Qed.



(** * Free variables in [formula] *)
Fixpoint ffreevars A :=
match A with
| var _ l => concat (map freevars l)
| imp B C => (ffreevars B) ++ (ffreevars C)
| frl x B => remove vatomEq.eq_dec x (ffreevars B)
end.

Lemma in_ffreevars_frl : forall x y, beq_vat y x = false -> forall A,
  In x (ffreevars A) -> In x (ffreevars (frl y A)).
Proof.
intros x y Heq A Hi ; simpl ; remember (ffreevars A) as l.
revert Hi ; clear - Heq ; induction l ; intros Hi ; auto.
inversion Hi ; subst ; simpl ; rcauto.
exfalso ; subst ; rewrite eqb_refl in Heq ; inversion Heq.
Qed.

Lemma ffreevars_fup : forall k A, ffreevars (fup k A) = ffreevars A.
Proof. formula_induction A. Qed.
Hint Rewrite ffreevars_fup.

Lemma nfree_subs : forall x u A, ~ In x (ffreevars A) -> subs x u A = A.
Proof. formula_induction A ; try rcauto.
- rnow apply nfree_tsubs then apply H.
- rnow apply H.
- rnow rewrite IHA.
  now apply H ; apply in_ffreevars_frl.
Qed.
Hint Rewrite nfree_subs using intuition ; fail.



(** * Hilbert style properties *)

(* Apply all (reversible) introduction rules *)
Ltac rev_intros := repeat (repeat apply rimpi ; repeat apply rfrli) ; apply rninj.

Lemma frl_elim : forall A u x, closed u -> rprove (frl x A :: nil) (subs x u A).
Proof. intros A u x Hf ; rev_intros.
apply (nfrle u) ; [ assumption | ].
apply nax_hd.
Qed.

Lemma frl_imp : forall A B x, rprove (frl x (imp A B) :: nil) (imp (frl x A) (frl x B)).
Proof. intros A B x ; rev_intros.
apply (nimpe (subs x (dvar 0) (fupz A))).
- change (imp (subs x (dvar 0) (fupz A)) (subs x (dvar 0) (fupz B)))
    with (subs x (dvar 0) (imp (fupz A) (fupz B))).
  apply nfrle ; [ reflexivity | ] ; simpl.
  change (frl x (fupz A) :: frl x (imp (fupz A) (fupz B)) :: nil)
    with ((frl x (fupz A) :: nil) ++ frl x (imp (fupz A) (fupz B)) :: nil).
  apply nax.
- apply rninj ; apply nfrle ; [ reflexivity | ].
  apply nax_hd.
Qed.

Lemma frl_nfree : forall A x, ~ In x (ffreevars A) -> rprove (A :: nil) (frl x A).
Proof. intros A x Hnf ; rev_intros.
rnow rewrite nfree_subs then apply nax_hd.
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
  + apply rninj ; apply nax_hd.
- apply rninj ; apply (nimpe A).
  + change (A :: imp A B :: imp A (imp B C) :: nil)
      with ((A :: nil) ++ imp A B :: imp A (imp B C) :: nil).
    apply nax.
  + apply rninj ; apply nax_hd.
Qed.




(** * More Lemmas *)

Lemma tsubs_tsubs_com : forall x v y u, beq_vat x y = false -> ~ In x (freevars u) -> forall t,
  tsubs y u (tsubs x v t) = tsubs x (tsubs y u v) (tsubs y u t).
Proof. term_induction t.
rnow case_eq (beq_vat x0 x) ; case_eq (beq_vat x0 y) then try rewrite H1 ; try rewrite H2.
exfalso.
now rewrite eqb_neq in H ; rewrite beq_eq_vat in H1 ; rewrite beq_eq_vat in H2 ; subst.
Qed.
Hint Rewrite tsubs_tsubs_com using try (intuition ; fail) ;
                                   (try apply closed_nofreevars) ; intuition ; fail.

Lemma subs_subs_com : forall x v y u, beq_vat x y = false -> closed u -> closed v ->
  forall A, subs y u (subs x v A) = subs x (tsubs y u v) (subs y u A).
Proof. induction A.
- simpl ; f_equal ; rnow rewrite 2 map_map ; apply map_ext.
  rnow idtac then rewrite (nfree_tsubs _ _ v) ; try now apply closed_nofreevars.
- rnow idtac then f_equal.
- (rnow case_eq (beq_vat v0 x) ; case_eq (beq_vat v0 y)) ;
    rnow rewrite H2 ; rewrite H3 ; simpl ; rewrite H2 ; rewrite H3 then f_equal.
Qed.
Hint Rewrite subs_subs_com using intuition ; fail.


(** * Examples *)
Section Examples.

Variable f : tatom.
Variable x y : vatom.
Variable P : atom.

Hint Rewrite eqb_refl.
Hint Rewrite (beq_eq_vat x y).

Goal forall A, rprove nil (imp (frl x (frl y A)) (frl y (frl x A))).
Proof.
intros ; apply rimpi ; repeat apply rfrli.
rnow (case_eq (beq_vat x y)) then rewrite H ; rev_intros.
- rnow apply nfrle.
  replace (frl x (fupz (fupz A)))
     with (subs x (dvar 0) (frl x (fupz (fupz A))))
    by rnow idtac.
  rnow apply nfrle then subst ; apply nax_hd.
- rnow idtac then rewrite subs_subs_com ; try rewrite eqb_sym.
  rnow apply nfrle.
  rewrite eqb_sym in H.
  replace (frl y (subs x (dvar 0) (fupz (fupz A))))
    with (subs x (dvar 0) (frl y (fupz (fupz A))))
    by (simpl ; rewrite H ; reflexivity).
  rnow apply nfrle then apply nax_hd.
Qed.

Goal rprove nil (imp (frl x (var P (tconstr f (tvar x :: nil) :: nil)))
                     (frl x (var P (tconstr f (tconstr f (tvar x :: nil) :: nil) :: nil)))).
Proof.
intros ; rev_intros ; rnow idtac.
replace (var P (tconstr f (tconstr f (dvar 0 :: nil) :: nil) :: nil))
   with (subs x (tconstr f (dvar 0 :: nil)) (var P (tconstr f (tvar x :: nil) :: nil)))
  by (rnow idtac).
apply nfrle ; [ reflexivity | ].
apply nax_hd.
Qed.


End Examples.


