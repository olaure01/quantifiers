(* Natural Deduction for First-Order Intuitionistic Logic *)

Require Import Lia.
Require Import stdlib_more.
Require Import fot_ar.

Import EqNotations.


(** * Formulas *)

Parameter atom : Type.  (* relation symbols for [formula] *)
Parameter arity : atom -> nat. (* arity of relation symbols *)

(** formulas *)
(** first-order formulas in the langage: implication, universal quantification *)
Inductive formula : nat -> Type :=
| rel : forall f, formula (arity f)
| fconstr : forall (t : term 0) {k}, formula (S k) -> formula k
| imp : formula 0 -> formula 0 -> formula 0
| frl : vatom -> formula 0 -> formula 0.

Ltac simpl_formula_induction F :=
  induction F ; try rcauto ; try (now intuition) ;
    try (simpl ; f_equal ; rnow try intuition).


(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k {m} (A : formula m) : formula m :=
match A with
| rel X => rel X
| fconstr t P => fconstr (tup k t) (fup k P)
| imp B C => imp (fup k B) (fup k C)
| frl x B => frl x (fup k B)
end.

Lemma fup_fup_com : forall k {m} (A : formula m),
  fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof. simpl_formula_induction A. Qed.
Hint Rewrite fup_fup_com : term_db.


(** substitutes [term] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint subs x u {m} (A : formula m) : formula m :=
match A with
| rel X => rel X
| fconstr t P => fconstr (tsubs x u t) (subs x u P)
| imp B C => imp (subs x u B) (subs x u C)
| frl y B as C => if (beq_vat y x) then C else frl y (subs x u B)
end.

Lemma fup_subs_com : forall k x u {m} (A : formula m),
  fup k (subs x u A) = subs x (tup k u) (fup k A).
Proof. simpl_formula_induction A. Qed.
Hint Rewrite fup_subs_com : term_db.

(** substitutes [term] [u] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint nsubs n u {m} (A : formula m) : formula m :=
match A with
| rel X => rel X
| fconstr t P => fconstr (ntsubs n u t) (nsubs n u P)
| imp B C => imp (nsubs n u B) (nsubs n u C)
| frl x B => frl x (nsubs n u B)
end.

Lemma nsubs_fup_com : forall k u {m} (A : formula m),
  nsubs (S k) (tup 0 u) (fup 0 A) = fup 0 (nsubs k u A).
Proof. simpl_formula_induction A. Qed.
Hint Rewrite nsubs_fup_com : term_db.

Lemma nsubs_z_fup : forall u {m} (A : formula m), nsubs 0 u (fup 0 A) = A.
Proof. simpl_formula_induction A. Qed.
Hint Rewrite nsubs_z_fup : term_db.

Lemma nsubs_subs_com : forall x v n u, ~ In x (freevars u) -> forall {m} (A : formula m),
  nsubs n u (subs x v A) = subs x (ntsubs n u v) (nsubs n u A).
Proof. simpl_formula_induction A. Qed.
Hint Rewrite nsubs_subs_com using try (intuition ; fail) ;
                                  (try apply closed_nofreevars) ; intuition ; fail : term_db.


(** size of formulas *)
Fixpoint fsize {m} (A : formula m) :=
match A with
| rel _ => 1
| fconstr _ _ => 1
| imp B C => S (fsize B + fsize C)
| frl _ B => S (fsize B)
end.

Lemma fsize_fup : forall k {m} (A : formula m), fsize (fup k A) = fsize A.
Proof. simpl_formula_induction A. Qed.
Hint Rewrite fsize_fup : term_db.

Lemma fsize_subs : forall u x {m} (A : formula m), fsize (subs x u A) = fsize A.
Proof. simpl_formula_induction A. Qed.
Hint Rewrite fsize_subs : term_db.




(** * Proofs *)

Notation fupz := (fup 0).
Notation fformula := (formula 0).

(** Proofs *)
Inductive prove : list fformula -> fformula -> Type :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi { l A B } : prove (A :: l) B -> prove l (imp A B)
| impe { l B } : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli { x l A } : prove (map fupz l) (subs x (dvar 0) (fupz A)) -> prove l (frl x A)
| frle { x l A } : forall u, closed u -> prove l (frl x A) -> prove l (subs x u A).
Hint Constructors prove : term_db.

(** Normal Forms *)
Inductive nprove : list fformula -> fformula -> Type :=
| nax : forall l1 l2 A, nprove (l1 ++ A :: l2) A
| nimpe { l B } : forall A, nprove l (imp A B) -> rprove l A -> nprove l B
| nfrle { x l A } : forall u, closed u -> nprove l (frl x A) -> nprove l (subs x u A)
with rprove : list fformula -> fformula -> Type :=
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
- assert (closed (tup 0 u)) by rnow idtac.
  specialize X with (S n) (tup 0 u).
  rewrite map_map in X ; rewrite (map_ext _ _ (nsubs_fup_com _ _)) in X ; rewrite <- map_map in X.
  rnow autorewrite with term_db in X.
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
  rnow change (dvar 0) with (tup (S k) (dvar 0)) in X.
  rewrite map_map in IH ; rewrite (map_ext _ _ (fup_fup_com _)) in IH ; rewrite <- map_map in IH.
  now apply rfrli.
Qed.





(** * Normalization *)

Theorem denormalization :
  (forall l A, nprove l A -> prove l A) * (forall l A, rprove l A -> prove l A).
Proof. apply rnprove_mutrect ; intros ; try (econstructor ; eassumption) ; assumption. Qed.

Lemma weakening :
   (forall l A, nprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> nprove (l1 ++ l0 ++ l2) A)
 * (forall l A, rprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> rprove (l1 ++ l0 ++ l2) A).
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
    inversion IH1 ; subst.
    * apply rninj ; eapply nimpe ; simpl...
    * remember (rsize X) as q.
      eapply (IHn _ (S q)) in IH2 ; [ | simpl in l3 | reflexivity ]...
      revert X Heqq ; rewrite <- (app_nil_l (A0 :: _)) ; intros H1 Heqq.
      refine (snd IH2 _ _ _ _ H1 eq_refl _)...
  + apply rninj ; eapply nimpe ; eapply pi1 ; simpl...
- apply (IHm (S (nsize pi2))) in pi1...
  assert (nsize pi2 < S (nsize pi2)) as IH1 by lia.
  destruct (Compare_dec.le_lt_dec (fsize (frl x A0)) (fsize A)).
  + eapply pi1 in IH1...
    inversion IH1 ; subst.
    * apply rninj ; eapply nfrle ; simpl...
    * apply (rnpsubs 0 u) in X...
      rnow rewrite map_map in X ; rewrite (map_ext _ _ (nsubs_z_fup _)) in X ;
           rewrite map_id in X.
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
  rewrite <- ? map_app ; apply (f_equal _ Hl).
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
  + apply (rnpsubs 0 u) in X...
    rnow rewrite map_map in X ; rewrite (map_ext _ _ (nsubs_z_fup _)) in X ;
         rewrite map_id in X.
Qed.



(** * Free variables in [formula] *)
Fixpoint ffreevars {m} (A : formula m) :=
match A with
| rel _ => nil
| fconstr t P => freevars t ++ (ffreevars P)
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

Lemma ffreevars_fup : forall k {m} (A : formula m), ffreevars (fup k A) = ffreevars A.
Proof. simpl_formula_induction A. Qed.
Hint Rewrite ffreevars_fup : term_db.

Lemma nfree_subs : forall x u {m} (A : formula m), ~ In x (ffreevars A) -> subs x u A = A.
Proof. simpl_formula_induction A; try now f_equal.
rnow rewrite IHA.
now apply H0 ; apply in_ffreevars_frl.
Qed.
Hint Rewrite nfree_subs using intuition ; fail : term_db.



(** * Hilbert style properties *)

(* Apply all (reversible) introduction rules *)
Ltac rev_intros := repeat (repeat apply rimpi ; repeat apply rfrli) ; apply rninj.

Lemma frl_elim : forall A u x, closed u -> rprove (frl x A :: nil) (subs x u A).
Proof. intros A u x Hf ; rev_intros.
rnow apply (nfrle u).
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
Proof with auto with term_db.
intros ; rev_intros.
change (B :: A :: nil) with ((B :: nil) ++ A :: nil)...
Qed.

Lemma Scombi : forall A B C, rprove nil (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).
Proof with auto with term_db.
intros ; rev_intros.
apply (nimpe B).
- apply (nimpe A)...
  change (A :: imp A B :: imp A (imp B C) :: nil)
    with ((A :: imp A B :: nil) ++ imp A (imp B C) :: nil)...
- apply rninj ; apply (nimpe A)...
  change (A :: imp A B :: imp A (imp B C) :: nil)
    with ((A :: nil) ++ imp A B :: imp A (imp B C) :: nil)...
Qed.




(** * More Lemmas *)

Lemma subs_subs_com : forall x v y u, beq_vat x y = false -> closed u -> closed v ->
  forall m (A : formula m), subs y u (subs x v A) = subs x (tsubs y u v) (subs y u A).
Proof. simpl_formula_induction A.
- (rnow case_eq (beq_vat v0 x) ; case_eq (beq_vat v0 y)) ; rnow rewrite H2.
- (rnow case_eq (beq_vat v0 x) ; case_eq (beq_vat v0 y)) ; rnow rewrite H2 ; f_equal.
Qed.
Hint Rewrite subs_subs_com using intuition ; fail : term_db.


(** * Examples *)
Section Examples.

Variable f : tatom.
Variable x y : vatom.
Variable P : atom.

Hypothesis farity : tarity f = 1.
Hypothesis Parity : arity P = 1.

Hint Rewrite eqb_refl : term_db.
Hint Rewrite (beq_eq_vat x y) : term_db.

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

Goal rprove nil
  (imp (frl x (fconstr (tconstr (tvar x) (rew farity in tfun f)) (rew Parity in rel P)))
       (frl x (fconstr (tconstr (tconstr (tvar x) (rew farity in tfun f))
                                                  (rew farity in tfun f)) (rew Parity in rel P)))).
Proof.
intros ; rev_intros ; rnow idtac.

replace
(fconstr
     (tconstr (tconstr (dvar 0) (tsubs x (dvar 0) (tup 0 (rew [term] farity in tfun f))))
        (tsubs x (dvar 0) (tup 0 (rew [term] farity in tfun f))))
     (subs x (dvar 0) (fupz (rew [formula] Parity in rel P))))
with
(fconstr
     (tconstr (tconstr (dvar 0) (rew [term] farity in tfun f))
        (rew [term] farity in tfun f))
     (rew [formula] Parity in rel P)).
replace (fconstr
     (tconstr (tconstr (dvar 0) (rew [term] farity in tfun f))
        (rew [term] farity in tfun f))
     (rew [formula] Parity in rel P))
 with (subs x (tconstr (dvar 0) (rew [term] farity in tfun f)) (fconstr
     (tconstr (tvar x)
        (rew [term] farity in tfun f))
     (rew [formula] Parity in rel P))).
{ apply nfrle.
- simpl.
  replace (closed (rew [term] farity in tfun f)) with (closed (tfun f)).
  + intuition.
  + rewrite <- farity ; reflexivity.
- replace (fconstr (tconstr (tvar x) (tup 0 (rew [term] farity in tfun f)))
                                     (fupz (rew [formula] Parity in rel P)))
    with (fconstr (tconstr (tvar x) (rew [term] farity in tfun f))
                                    (rew [formula] Parity in rel P)).
  apply nax_hd.

  f_equal ; try f_equal.
  + rewrite <- farity ; reflexivity.
  + rewrite <- Parity ; reflexivity. }

- simpl ; f_equal ; try f_equal.
  + rewrite eqb_refl ; reflexivity.
  + remember (tconstr (dvar 0) (rew [term] farity in tfun f)) as u.
    rewrite <- farity ; reflexivity.
  + rewrite <- Parity ; reflexivity.
- f_equal ; try f_equal ; try f_equal.
  + rewrite <- farity ; reflexivity.
  + rewrite <- farity ; reflexivity.
  + rewrite <- Parity ; reflexivity.
Qed.

End Examples.



