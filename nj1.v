(* Natural Deduction for First-Order Intuitionistic Logic *)

Require Import Wf_nat_more. (* from ollibs *)
Require Import Lia.

Require Import fot.


(* * Preliminaries *)

Lemma Exists_impl {A} : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
  forall l, Exists P l -> Exists Q l.
Proof.
intros P Q Hi.
induction l ; intros He ; inversion He ; subst.
- apply Hi in H0 ; now constructor.
- apply IHl in H0 ; now constructor.
Qed.




(** * Formulas *)

Parameter atom : Type.  (* relation symbols for [formula] *)

(** formulas *)
(** first-order formulas in the langage: implication, universal quantification *)
Inductive formula :=
| var : atom -> list term -> formula
| imp : formula -> formula -> formula
| frl : vatom -> formula -> formula
| exs : vatom -> formula -> formula.

Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | A1 A2 | xx A | xx A ] ; simpl ; intros ;
  [ try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; intuition ;
                       rewrite IHll ; f_equal ; intuition)
  | try (f_equal ; intuition)
  | try (f_equal ; intuition)
  | try (f_equal ; intuition) ] ; try ((rnow idtac) ; fail) ; try (rcauto ; fail).

(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X l => var X (map (tup k) l)
| imp B C => imp (fup k B) (fup k C)
| frl x B => frl x (fup k B)
| exs x B => exs x (fup k B)
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
| exs y B as C => if (beq_vat y x) then C else exs y (subs x u B)
end.

Lemma fup_subs_com : forall k x u A,
  fup k (subs x u A) = subs x (tup k u) (fup k A).
Proof. formula_induction A.
all: rnow case_eq (beq_vat x0 x) ; intros ; simpl ; f_equal.
Qed.
Hint Rewrite fup_subs_com.

(** substitutes [term] [u] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint nsubs n u A :=
match A with
| var X l => var X (map (ntsubs n u) l)
| imp B C => imp (nsubs n u B) (nsubs n u C)
| frl x B => frl x (nsubs n u B)
| exs x B => exs x (nsubs n u B)
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
| exs _ B => S (fsize B)
end.

Lemma fsize_fup : forall k A, fsize (fup k A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_fup.

Lemma fsize_subs : forall u x A, fsize (subs x u A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_subs.

Lemma fsize_nsubs : forall u n A, fsize (nsubs n u A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_nsubs.


(** Sub-formula Relation *)
Inductive subform : formula -> formula -> Prop :=
| sub_id : forall A, subform A A
| sub_imp_l : forall A B C, subform A B -> subform A (imp B C)
| sub_imp_r : forall A B C, subform A B -> subform A (imp C B)
| sub_frl : forall A x u B, subform A (subs x u B) -> subform A (frl x B)
| sub_ex : forall A x u B, subform A (subs x u B) -> subform A (exs x B)
| sub_frl_n : forall A x B, subform A (subs x (dvar 0) (fup 0 B)) -> subform A (frl x B)
| sub_ex_n : forall A x B, subform A (subs x (dvar 0) (fup 0 B)) -> subform A (exs x B)
| sub_fup : forall A B, subform A (fup 0 B) -> subform A B.

Lemma subform_trans : forall A B C, subform A B -> subform B C -> subform A C.
Proof with try assumption.
intros A B C Hl Hr ; revert A Hl ; induction Hr ; intros A' Hl ;
  try (econstructor ; apply IHHr)...
Qed.


(** * Proofs *)

Notation fupz := (fup 0).

(** Proofs *)
Inductive prove : list formula -> formula -> Type :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi { l A B } : prove (A :: l) B -> prove l (imp A B)
| impe { l B } : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli { x l A } : prove (map fupz l) (subs x (dvar 0) (fupz A)) -> prove l (frl x A)
| frle { x l A } : forall u, closed u -> prove l (frl x A) -> prove l (subs x u A)
| exsi { x l A } : forall u, closed u -> prove l (subs x u A) -> prove l (exs x A)
| exse { x l C } : forall A, prove l (exs x A) ->
                             prove (subs x (dvar 0) (fupz A) :: map fupz l) (fupz C) -> prove l C.
Hint Constructors prove.

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
Hint Constructors nprove rprove.

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
       (forall (x : vatom) (l : list formula) (A : formula) (u : term)
         (e : closed u) (n : nprove l (frl x A)),
        P l (frl x A) n -> P l (subs x u A) (nfrle u e n)) ->
       (forall (l : list formula) (A : formula) (n : nprove l A), P l A n -> P0 l A (rninj n)) ->
       (forall (l : list formula) (A B : formula) (r : rprove (A :: l) B),
        P0 (A :: l) B r -> P0 l (imp A B) (rimpi r)) ->
       (forall (x : vatom) (l : list formula) (A : formula)
          (r : rprove (map fupz l) (subs x (dvar 0) (fupz A))),
        P0 (map fupz l) (subs x (dvar 0) (fupz A)) r -> P0 l (frl x A) (rfrli r)) ->
       (forall (x : vatom) (l : list formula) (A : formula) (u : term) (e : closed u)
          (r : rprove l (subs x u A)),
        P0 l (subs x u A) r -> P0 l (exs x A) (rexsi u e r)) ->
       (forall (l : list formula) (C : formula) (x : vatom) (A : formula) (n : nprove l (exs x A)),
        P l (exs x A) n ->
        forall r : rprove (subs x (dvar 0) (fupz A) :: map fupz l) (fupz C),
        P0 (subs x (dvar 0) (fupz A) :: map fupz l) (fupz C) r -> P0 l C (rexse x A n r)) ->
(*
       (forall (l : list formula) (f7 : formula) (n : nprove l f7), P l f7 n) /\
       (forall (l : list formula) (f7 : formula) (r : rprove l f7), P0 l f7 r).
*)
       forall (l : list formula) (f7 : formula),
         ((forall (n : nprove l f7), P l f7 n) * (forall (n : rprove l f7), P0 l f7 n)).
Proof.
intros ; split ; [ eapply nrprove_rect | eapply rnprove_rect ] ; eassumption.
Qed.

Lemma nax_hd {l A} : nprove (A :: l) A.
Proof. rewrite <- (app_nil_l (A :: l)) ; apply nax. Qed.
Hint Resolve nax_hd.

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


(* property [P] holds for any formula in [pi] *)
Fixpoint nprove_with_prop P {l A} (pi : nprove l A) : Prop :=
match pi with
| nax l1 l2 A  => Forall P l1 /\ Forall P l2 /\ P A
| @nimpe _ B _ pi1 pi2 => P B /\ nprove_with_prop P pi1 /\ rprove_with_prop P pi2
| @nfrle x _ A u _ pi0 => P (subs x u A) /\ nprove_with_prop P pi0
end
with rprove_with_prop P {l A} (pi : rprove l A) : Prop :=
match pi with
| rninj pi0 => nprove_with_prop P pi0
| @rimpi _ A B pi0 => P (imp A B) /\ rprove_with_prop P pi0
| @rfrli x _ A pi0 => P (frl x A) /\ rprove_with_prop P pi0
| @rexsi x _ A _ _ pi0 => P (exs x A) /\ rprove_with_prop P pi0
| @rexse _ C _ _ pi1 pi2 => P C /\ nprove_with_prop P pi1 /\ rprove_with_prop P pi2
end.

Lemma rnprove_stronger : forall (P Q : _ -> Prop), (forall x, P x -> Q x) -> forall l A,
   (forall pi : nprove l A, nprove_with_prop P pi -> nprove_with_prop Q pi)
 * (forall pi : rprove l A, rprove_with_prop P pi -> rprove_with_prop Q pi).
Proof.
intros P Q Hs l A.
apply (rnprove_mutrect
  (fun l' B (p : nprove l' B) => nprove_with_prop P p -> nprove_with_prop Q p)
  (fun l' B (p : rprove l' B) => rprove_with_prop P p -> rprove_with_prop Q p)) ; simpl ; intuition.
- eapply Forall_impl ; eassumption.
- eapply Forall_impl ; eassumption.
Qed.

Theorem subformula_prop {l A} :
   (forall pi : nprove l A, Exists (subform A) l /\ nprove_with_prop (fun B => Exists (subform B) (A :: l)) pi)
 * (forall pi : rprove l A, rprove_with_prop (fun B => Exists (subform B) (A :: l)) pi).
Proof.
apply (rnprove_mutrect
  (fun l' B (p : nprove l' B) => Exists (subform B) l'
                            /\   nprove_with_prop (fun C => Exists (subform C) (B :: l')) p)
  (fun l' B (p : rprove l' B) => rprove_with_prop (fun C => Exists (subform C) (B :: l')) p)) ; simpl.
- intros l1 l2 B ; repeat split.
  + apply Exists_exists ; exists B ; split ; [ | constructor ].
    apply in_app_iff ; right ; constructor ; reflexivity.
  + rewrite <- (app_nil_l l1) ; rewrite <- app_assoc ; rewrite app_comm_cons.
    remember (B :: nil) as l0 ; clear Heql0 ; revert l0.
    induction l1 ; intros l0 ; constructor.
    * apply Exists_exists ; exists a ; split ; [ | constructor ].
       apply in_app_iff ; right ; constructor ; reflexivity.
    * rewrite <- app_comm_cons ; rewrite <- (app_nil_l l1) ; rewrite <- app_assoc ;
        rewrite app_comm_cons ; rewrite app_assoc.
      apply IHl1.
  + rewrite <- (app_nil_l l2) ; rewrite 2 app_comm_cons ; rewrite app_assoc.
    remember ((B :: l1) ++ B :: nil) as l0 ; clear Heql0 ; revert l0 ; simpl.
    induction l2 ; intros l0 ; constructor.
    * apply Exists_exists ; exists a ; split ; [ | constructor ].
       apply in_app_iff ; right ; constructor ; reflexivity.
    * rewrite <- (app_nil_l l2) ; rewrite app_comm_cons ; rewrite app_assoc.
      apply IHl2.
  + constructor ; constructor.
- intros l' B' A' pi1 [Hn Hs1] pi2 Hs2 ; repeat split.
  + eapply Exists_impl ; [ | eassumption ].
    intros C HsC.
    now eapply subform_trans ; [ constructor ; constructor | eassumption ].
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      eapply subform_trans ; eassumption.
    * constructor ; assumption.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      eapply subform_trans ; [ eassumption | ].
      eapply subform_trans ; [ constructor ; constructor | eassumption ].
    * constructor ; assumption.
- intros x l' A' u Hc pi [Hn Hs] ; repeat split.
  + eapply Exists_impl ; [ | eassumption ].
    intros C HsC.
    eapply subform_trans ; [ econstructor ; constructor | eassumption ].
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      eapply subform_trans ; eassumption.
    * constructor ; assumption.
- intros.
  apply H.
- intros l' A' B' pi Hs ; split.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | apply Hs ] ; simpl.
    intros C P.
    inversion P ; subst.
    * constructor ; now constructor.
    * inversion H0 ; subst.
      -- constructor ; now constructor.
      -- constructor ; assumption.
- intros x l' A' pi Hs ; split.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | apply Hs ] ; simpl.
    intros C P.
    inversion P ; subst.
    * constructor.
      eapply subform_trans ; [ eassumption | constructor ; constructor ].
    * apply Exists_cons_tl.
      revert H0 ; clear ; induction l' ; intros H ; inversion H ; subst.
      -- constructor.
         eapply subform_trans ; [ eassumption | constructor ; constructor ].
      -- apply Exists_cons_tl ; intuition.
- intros x l' A' u Hc pi Hs ; split.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | apply Hs ] ; simpl.
    intros C P.
    inversion P ; subst.
    * constructor.
      eapply subform_trans ; [ eassumption | econstructor ; constructor ].
    * constructor ; assumption.
- intros l' C x A' pi1 [Hn Hs1] pi2 Hs2 ; repeat split.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros D HsD.
    inversion HsD ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros E HsE.
      eapply subform_trans ; eassumption.
    * constructor ; assumption.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros D HsD.
    inversion HsD ; subst.
    * constructor.
      eapply subform_trans ; [ eassumption | constructor ; constructor ].
    * inversion H0 ; subst ; apply Exists_cons_tl.
      -- eapply Exists_impl ; [ | eassumption ].
         intros E HsE.
         eapply subform_trans ; [ eassumption | ].
         eapply subform_trans ; [ constructor ; constructor | eassumption ].
      -- revert H1 ; clear ; induction l' ; intros H ; inversion H ; subst.
         ++ constructor.
            eapply subform_trans ; [ eassumption | constructor ; constructor ].
         ++ apply Exists_cons_tl ; intuition.
Qed.



(** substitutes [term] [u] for index [n] in normal form and decreases indexes above [n] *)
Theorem rnpsubs n u (Hc : closed u) {l A} :
   (nprove l A -> nprove (map (nsubs n u) l) (nsubs n u A))
 * (rprove l A -> rprove (map (nsubs n u) l) (nsubs n u A)).
Proof with try eassumption.
enough ((nprove l A -> forall n u, closed u -> nprove (map (nsubs n u) l) (nsubs n u A))
      * (rprove l A -> forall n u, closed u -> rprove (map (nsubs n u) l) (nsubs n u A)))
  as He by (split ; intros ; apply He ; assumption).
clear n u Hc ; revert l A ; apply rnprove_mutrect ;
  intros ; (try simpl in X) ;
  (try assert (IH1 := X n0 u H)) ; (try assert (IH2 := X0 n0 u H)) ; 
  (try (econstructor ; (eassumption + intuition) ; fail)).
- rewrite map_app ; apply nax.
- rnow idtac then rnow eapply nfrle.
- assert (closed (tup 0 u)) by rnow idtac.
  specialize X with (S n) (tup 0 u).
  rewrite map_map in X ; rewrite (map_ext _ _ (nsubs_fup_com _ _)) in X ; rewrite <- map_map in X.
  rnow autorewrite with core in X.
- rnow specialize X with n u0 then rnow eapply (rexsi (ntsubs n u0 u)).
- rewrite <- (freevars_tup 0) in H.
  clear IH2 ; assert (IH2 := X0 (S n0) (tup 0 u) H) ; simpl in IH2.
  rewrite map_map in IH2 ; rewrite (map_ext _ _ (nsubs_fup_com _ _)) in IH2 ;
    rewrite <- map_map in IH2.
  rnow eapply rexse.
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
  intros ; (try assert (IH1 := X k)) ; (try assert (IH2 := X0 k)) ;
  (try (econstructor ; eassumption ; fail)).
- rewrite map_app ; apply nax.
- rnow idtac then rnow apply nfrle.
- clear IH1 ; assert (IH := X (S k)).
  rnow change (dvar 0) with (tup (S k) (dvar 0)) in X.
  rewrite map_map in IH ; rewrite (map_ext _ _ (fup_fup_com _)) in IH ; rewrite <- map_map in IH.
  now apply rfrli.
- rnow idtac then rnow apply (rexsi (tup k u)).
- clear IH2 ; assert (IH2 := X0 (S k)) ; simpl in IH2.
  rnow change (dvar 0) with (tup (S k) (dvar 0)) in X.
  rewrite map_map in IH2 ; rewrite (map_ext _ _ (fup_fup_com _)) in IH2 ; rewrite <- map_map in IH2.
  rnow apply (rexse x (fup k A)).
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
- apply rfrli ; rewrite ? map_app ; apply X ; rewrite map_app ; reflexivity.
- apply (rexsi u) ; [ assumption | apply X ; reflexivity ].
- apply (rexse x A).
  + apply X ; reflexivity.
  + rewrite ? map_app ; rewrite app_comm_cons ; apply X0 ; rewrite map_app ; reflexivity.
Qed.

Lemma substitution : forall n m l A, fsize A = n -> rprove l A ->
   (forall B l0 l1 l2 (pi : nprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
      nsize pi < m -> fsize A < fsize B -> nprove (l1 ++ l2) B)
 * (forall B l0 l1 l2 (pi : nprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
      nsize pi < m -> rprove (l1 ++ l2) B)
 * (forall B l0 l1 l2 (pi : rprove (l1 ++ A :: l2) B), l0 ++ l = l1 ++ l2 ->
      rsize pi < m -> rprove (l1 ++ l2) B).
Proof with try eassumption ; try reflexivity ; try lia.
apply (lt_wf_double_rect (fun n m =>
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
    remember (imp A0 B) as C.
    clear r pi1 Hpi.
    revert A0 B HeqC l3 IH2 ; clear - IHn IH1 ; induction IH1 ;
      intros A1 B1 HeqC Hs IH2 ; inversion HeqC ; subst.
    * apply rninj ; eapply nimpe...
    * remember (rsize IH1) as q.
      eapply (IHn _ (S q)) in IH2 ; [ | simpl in Hs | reflexivity ]...
      revert IH1 Heqq ; rewrite <- (app_nil_l (A1 :: _)) ; intros IH1 Heqq.
      refine (snd IH2 _ _ _ _ IH1 eq_refl _)...
    * rnow simpl in IHIH1 then simpl in IH1.
      eapply rexse...
      eapply IHIH1 ; [ reflexivity | | ]...
      rewrite <- (app_nil_l (map fupz l)) ; rewrite app_comm_cons ; rewrite <- (app_nil_l _).
      eapply weakening ; [ | reflexivity ].
      apply rnpup...
  + apply rninj ; eapply nimpe ; eapply pi1...
- apply (IHm (S (nsize pi2))) in pi1...
  assert (nsize pi2 < S (nsize pi2)) as IH1 by lia.
  destruct (Compare_dec.le_lt_dec (fsize (frl x A0)) (fsize A)).
  + eapply pi1 in IH1...
    remember (frl x A0) as C.
    revert u e A0 HeqC l3 ; clear - IHn IH1 ; induction IH1 ;
      intros u' e' A1 HeqC Hs ; inversion HeqC ; subst.
    * apply rninj ; eapply nfrle...
    * apply (rnpsubs 0 u') in IH1...
      rnow rewrite map_map in IH1 ; rewrite (map_ext _ _ (nsubs_z_fup _)) in IH1 ;
           rewrite map_id in IH1.
    * rnow simpl in IHIH1 then simpl in IH1.
      eapply rexse...
      rnow idtac then rnow (eapply IHIH1).
  + apply rninj ; eapply nfrle...
    eapply pi1...
- refine (snd (fst (IHm _ Hpi _ _ _ pi1)) _ _ _ _ n _ _)...
- revert pi2 Hpi ; rewrite app_comm_cons ; intros pi2 Hpi.
  apply rimpi.
  refine (snd (IHm _ Hpi _ _ _ pi1) _ _ _ _ pi2 _ _)...
  simpl ; rewrite <- Hl ; rewrite app_comm_cons...
- apply rfrli ; rewrite map_app.
  apply (rnpup 0) in pi1.
  revert pi2 Hpi ; rewrite map_app ; simpl ; intros pi2 Hpi.
  rnow refine (snd (IHm _ Hpi _ _ _ pi1) _ (map fupz l0) _ _ pi2 _ _)...
  rewrite <- ? map_app ; f_equal...
- eapply rexsi...
  refine (snd (IHm _ Hpi _ _ _ pi1) _ _ _ _ pi2 _ _)...
- assert (nsize n < S (nsize n + rsize pi2)) as IH1 by lia.
  assert (rsize pi2 < S (nsize n + rsize pi2)) as IH2 by lia.
  destruct (Compare_dec.le_lt_dec (fsize (exs x A0)) (fsize A)).
  + assert (pi1' := pi1).
    apply (IHm (S (nsize n + rsize pi2))) in pi1'...
    eapply pi1' in IH1 ; clear pi1'...
    apply (rnpup 0) in pi1.
    apply (IHm (S (nsize n + rsize pi2))) in pi1 ; autorewrite with core...
    revert pi2 pi1 Hpi IH2 ; rewrite map_app ; simpl ; rewrite app_comm_cons ;
      intros pi2 pi1 Hpi IH2.
    eapply pi1 in IH2 ; simpl ;
      [ | rewrite <- (map_app _ _ l2) ; rewrite <- Hl ; rewrite map_app ; rewrite app_comm_cons ]...
    clear Hpi pi1 pi2 Hl n.
    remember (l1 ++ l2) as ll.
    remember (exs x A0) as D.
    revert x A0 C HeqD l1 l2 Heqll l3 IH2 ; clear - IHn IH1 ; induction IH1 ;
      intros x1 A1 C1 HeqD l1 l2 Heqll Hs IH2 ; inversion HeqD ; subst.
    * simpl in IH2 ; rewrite <- map_app in IH2.
      eapply rexse...
    * apply (rnpsubs 0 u) in IH2...
      rnow simpl in IH2 then simpl in IH2 ; rewrite map_app in IH2.
      do 2 (rewrite map_map in IH2 ; rewrite (map_ext _ _ (nsubs_z_fup _)) in IH2 ;
            rewrite map_id in IH2).
      remember (rsize IH2) as q.
      eapply (IHn (fsize _) (S q)) in IH1 ; [ | rnow simpl in Hs | autorewrite with core ]...
      revert IH2 Heqq ; rewrite <- (app_nil_l (subs x1 u A1 :: _)) ; intros IH2 Heqq.
      refine (snd IH1 _ _ _ _ IH2 eq_refl _)...
    * rnow simpl in IHIH1 then simpl in IH1.
      eapply rexse...
      eapply IHIH1 ; [ reflexivity | rewrite map_app ; rewrite app_comm_cons | | ]...
      simpl ; rewrite <- (app_nil_l (fupz _ :: _)) ; rewrite app_comm_cons ;
        rewrite <- (app_nil_l (map fupz _)) ; rewrite <- app_assoc ; rewrite app_comm_cons.
      eapply weakening ; [ | reflexivity ] ; simpl.
      apply (rnpup 1) in IH2 ; rnow simpl in IH2 then simpl in IH2 ; rewrite map_app in IH2.
      rewrite map_map in IH2 ; rewrite (map_ext _ _ (fup_fup_com _)) in IH2 ;
        rewrite <- map_map in IH2.
      rewrite (map_map _ _ l2) in IH2 ; rewrite (map_ext _ _ (fup_fup_com _)) in IH2 ;
        rewrite <- (map_map _ _ l2) in IH2...
  + eapply rexse.
    * refine (fst (fst (IHm _ _ _ _ _ _)) _ _ _ _ _ _ _ l3)...
    * clear IH1.
      revert pi2 Hpi IH2 ; rewrite map_app ; simpl ; rewrite app_comm_cons ; intros pi2 Hpi IH2.
      rewrite map_app ; rewrite app_comm_cons.
      apply (rnpup 0) in pi1.
      refine (snd (IHm _ _ _ _ _ _) _ _ _ _ _ _ IH2) ; [ | autorewrite with core | | ]...
      simpl ; rewrite <- (map_app _ _ l2) ; rewrite <- Hl ; rewrite map_app ; rewrite app_comm_cons...
Qed.

Lemma smp_substitution : forall l A B, rprove l A -> rprove (A :: l) B -> rprove l B.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A B pi1 pi2.
rewrite <- (app_nil_l (A :: l)) in pi2 ; rewrite <- (app_nil_l l).
refine (snd (substitution _ (S (rsize pi2)) _ _ _ pi1) _ _ _ _ pi2 _ _)...
Qed.


Theorem normalization : forall l A, prove l A -> rprove l A.
Proof with try eassumption ; try reflexivity.
intros l A pi ; induction pi ;
  try (constructor ; assumption) ;
  try (do 2 constructor ; assumption).
- remember (imp A B) as C.
  clear pi1 pi2 ; revert A B HeqC IHpi2 ; induction IHpi1 ;
    intros A1 B2 HeqC IHpi2 ; inversion HeqC ; subst.
  + apply rninj ; eapply nimpe...
  + eapply smp_substitution...
  + eapply rexse...
    eapply IHIHpi1 ; [ simpl ; reflexivity | ].
    apply (rnpup 0) in IHpi2.
    rewrite <- (app_nil_l (map fupz _)) ; rewrite app_comm_cons ; rewrite <- (app_nil_l _).
    eapply weakening...
- remember (frl x A) as C.
  clear pi ; revert x u e A HeqC ; induction IHpi ; intros x1 u1 e1 A1 HeqC ; inversion HeqC ; subst.
  + apply rninj ; eapply nfrle...
  + apply (rnpsubs 0 u1) in IHpi...
    rnow rewrite map_map in IHpi ; rewrite (map_ext _ _ (nsubs_z_fup _)) in IHpi ;
         rewrite map_id in IHpi.
  + eapply rexse...
    rnow idtac then rnow (eapply IHIHpi).
- eapply rexsi...
- remember (exs x A) as D.
  clear pi1 pi2 ; revert A C HeqD IHpi2 ; induction IHpi1 ;
    intros A1 C1 HeqD IHpi2 ; inversion HeqD ; subst.
  + eapply rexse...
  + apply (rnpsubs 0 u) in IHpi2...
    rnow simpl in IHpi2 then simpl in IHpi2.
    rewrite map_map in IHpi2 ; rewrite (map_ext _ _ (nsubs_z_fup _)) in IHpi2 ;
      rewrite map_id in IHpi2.
    eapply smp_substitution...
  + rnow simpl in IHIHpi1 then simpl in IHpi1.
    eapply rexse...
    eapply IHIHpi1 ; [ reflexivity |  ]...
    simpl ; rewrite <- (app_nil_l (subs x0 _ _ :: _)) ; rewrite app_comm_cons ;
      rewrite <- (app_nil_l (map fupz _)) ; rewrite app_comm_cons.
    eapply weakening ; [ | reflexivity ] ; simpl.
    apply (rnpup 1) in IHpi2 ; rnow simpl in IHpi2 then simpl in IHpi2.
    rewrite map_map in IHpi2 ; rewrite (map_ext _ _ (fup_fup_com _)) in IHpi2 ;
      rewrite <- map_map in IHpi2...
Qed.



(** * Free variables in [formula] *)
Fixpoint ffreevars A :=
match A with
| var _ l => concat (map freevars l)
| imp B C => (ffreevars B) ++ (ffreevars C)
| frl x B => remove vatomEq.eq_dec x (ffreevars B)
| exs x B => remove vatomEq.eq_dec x (ffreevars B)
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
- rnow rewrite IHA.
  now apply H ; apply in_ffreevars_frl.
Qed.
Hint Rewrite nfree_subs using intuition ; fail.



(** * Hilbert style properties *)

(* Apply all (reversible) introduction rules *)
Ltac rev_intros := repeat (repeat apply rimpi ; repeat apply rfrli) ; apply rninj.

Lemma frl_elim : forall A u x, closed u -> rprove (frl x A :: nil) (subs x u A).
Proof. intros A u x Hf ; rev_intros.
now apply (nfrle u).
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
rnow rewrite nfree_subs.
Qed.

Lemma Kcombi : forall A B, rprove nil (imp A (imp B A)).
Proof.
intros ; rev_intros.
now change (B :: A :: nil) with ((B :: nil) ++ A :: nil).
Qed.

Lemma Scombi : forall A B C, rprove nil (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).
Proof.
intros ; rev_intros.
apply (nimpe B).
- apply (nimpe A) ; auto.
  now change (A :: imp A B :: imp A (imp B C) :: nil)
        with ((A :: imp A B :: nil) ++ imp A (imp B C) :: nil).
- apply rninj ; apply (nimpe A) ; auto.
  now change (A :: imp A B :: imp A (imp B C) :: nil)
        with ((A :: nil) ++ imp A B :: imp A (imp B C) :: nil).
Qed.




(** * More Lemmas *)

Lemma subs_subs_com : forall x v y u, beq_vat x y = false -> closed u -> closed v ->
  forall A, subs y u (subs x v A) = subs x (tsubs y u v) (subs y u A).
Proof. induction A.
- simpl ; f_equal ; rnow rewrite 2 map_map ; apply map_ext.
  rnow idtac then rewrite (nfree_tsubs _ _ v) ; try now apply closed_nofreevars.
- rnow idtac then f_equal.
- (rnow case_eq (beq_vat v0 x) ; case_eq (beq_vat v0 y)) ;
    rnow rewrite H2 ; rewrite H3 ; simpl ; rewrite H2 ; rewrite H3 then f_equal.
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
  rnow apply nfrle then subst.
- rnow idtac then rewrite subs_subs_com ; try rewrite eqb_sym.
  rnow apply nfrle.
  rewrite eqb_sym in H.
  replace (frl y (subs x (dvar 0) (fupz (fupz A))))
    with (subs x (dvar 0) (frl y (fupz (fupz A))))
    by (simpl ; rewrite H ; reflexivity).
  rnow apply nfrle.
Qed.

Goal rprove nil (imp (frl x (var P (tconstr f (tvar x :: nil) :: nil)))
                     (frl x (var P (tconstr f (tconstr f (tvar x :: nil) :: nil) :: nil)))).
Proof.
intros ; rev_intros ; rnow idtac.
replace (var P (tconstr f (tconstr f (dvar 0 :: nil) :: nil) :: nil))
   with (subs x (tconstr f (dvar 0 :: nil)) (var P (tconstr f (tvar x :: nil) :: nil)))
  by (rnow idtac).
now apply nfrle.
Qed.

End Examples.



