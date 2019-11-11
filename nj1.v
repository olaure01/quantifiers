(* Natural Deduction for First-Order Intuitionistic Logic *)

Require Import Lia.
Require Import stdlib_more.
Require Export fot.

Set Implicit Arguments.


(** * Formulas and Proofs *)

Section Formulas.

Context { vatom : DecType } { tatom : Type }.
Notation term := (@term vatom tatom).
Notation closed t := (freevars t = nil).
Notation tup := (@tup vatom tatom).

Hint Rewrite
  (@tup_tup_com vatom tatom) (@tup_tsubs_com vatom tatom)
  (@ntsubs_tup_com vatom tatom) (@ntsubs_z_tup vatom tatom)
  (@freevars_tup vatom tatom) (@tsubs_tsubs_eq vatom tatom) : term_db.
Hint Resolve (@closed_nofreevars vatom tatom) : term_db.
Hint Rewrite (@freevars_ntsubs vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@nfree_tsubs vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@ntsubs_tsubs_com vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@tsubs_tsubs_com vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@freevars_tsubs_closed vatom tatom)
  using intuition; fail : term_db.

Context { fatom : Type }.  (* relation symbols for [formula] *)

(** formulas *)
(** first-order formulas in the langage: implication, universal quantification *)
Inductive formula :=
| var : fatom -> list term -> formula
| imp : formula -> formula -> formula
| frl : vatom -> formula -> formula
| exs : vatom -> formula -> formula.
(* alternative representation (thanks D. Pous)
Inductive qtf := Frl | Exs.  (* use bool *)
Inductive qformula :=
| qvar : fatom -> list term -> qformula
| qimp : qformula -> qformula -> qformula
| qant : qtf -> vatom -> qformula -> qformula.
Notation qfrl := (qant Frl).
Notation qexs := (qant Exs).
(* could be generalized to a family of binary connectives,
   a family of unary connectives, etc
*)
*)

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
  induction A as [ XX ll | A1 A2 | xx A | xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try f_equal; try (induction ll as [ | tt lll IHll ]; simpl; intuition;
                      rewrite IHll; f_equal; intuition)
  | try (f_equal; intuition)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail) ];
  try (now (rnow idtac)); try (now rcauto).

(** lift indexes above [k] in [formula] [A] *)
Fixpoint fup k A :=
match A with
| var X l => var X (map (tup k) l)
| imp B C => imp (fup k B) (fup k C)
| frl x B => frl x (fup k B)
| exs x B => exs x (fup k B)
end.
Notation fupz := (fup 0).

Lemma fup_fup_com : forall k A, fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof. formula_induction A. Qed.
Hint Rewrite fup_fup_com : term_db.


(** substitutes [term] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint subs x u A :=
match A with
| var X l => var X (map (tsubs x u) l)
| imp B C => imp (subs x u B) (subs x u C)
| frl y B => frl y (if (eqb y x) then B else subs x u B)
| exs y B => exs y (if (eqb y x) then B else subs x u B)
end.

Lemma fup_subs_com : forall k x u A,
  fup k (subs x u A) = subs x (tup k u) (fup k A).
Proof. formula_induction A. Qed.
Hint Rewrite fup_subs_com : term_db.

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
Hint Rewrite nsubs_fup_com : term_db.

Lemma nsubs_z_fup : forall u A, nsubs 0 u (fup 0 A) = A.
Proof. formula_induction A. Qed.
Hint Rewrite nsubs_z_fup : term_db.

Lemma nsubs_subs_com : forall x v n u, ~ In x (freevars u) -> forall A,
  nsubs n u (subs x v A) = subs x (ntsubs n u v) (nsubs n u A).
Proof. formula_induction A. Qed.
Hint Rewrite nsubs_subs_com using try (intuition ; fail) ;
                                  (try apply closed_nofreevars) ; intuition ; fail : term_db.


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
Hint Rewrite fsize_fup : term_db.

Lemma fsize_subs : forall u x A, fsize (subs x u A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_subs : term_db.

Lemma fsize_nsubs : forall u n A, fsize (nsubs n u A) = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_nsubs : term_db.


(** * Proofs *)

(** Proofs *)
Inductive prove : list formula -> formula -> Type :=
| ax : forall l1 l2 A, prove (l1 ++ A :: l2) A
| impi { l A B } : prove (A :: l) B -> prove l (imp A B)
| impe { l B } : forall A, prove l (imp A B) -> prove l A -> prove l B
| frli { x l A } : prove (map fupz l) (subs x (dvar 0) (fupz A)) -> prove l (frl x A)
| frle { x l A } : forall u, closed u -> prove l (frl x A) -> prove l (subs x u A)
| exsi { x l A } : forall u, closed u -> prove l (subs x u A) -> prove l (exs x A)
| exse { l C } : forall x A, prove l (exs x A) ->
                             prove (subs x (dvar 0) (fupz A) :: map fupz l) (fupz C) -> prove l C.
Hint Constructors prove : term_db.
Global Arguments impe { l B } _ _ _.
Global Arguments exse { l C } _ _ _.

Lemma ax_hd {l A} : prove (A :: l) A.
Proof. rewrite <- (app_nil_l (A :: l)); apply ax. Qed.

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
Global Arguments nimpe { l B } _ _ _.
Global Arguments rexse { l C } _ _ _ _.

Scheme nrprove_rect := Induction for nprove Sort Type
  with rnprove_rect := Induction for rprove Sort Type.
Combined Scheme rnprove_mutrect from nrprove_rect, rnprove_rect.

Lemma nax_hd {l A} : nprove (A :: l) A.
Proof. rewrite <- (app_nil_l (A :: l)); apply nax. Qed.
Hint Resolve nax_hd : term_db.

(* automatic tactic for application of the [nax] constructor *)
Ltac run_nax :=
  match goal with
  | |- nprove (?l1 ++ ?B :: ?l2) ?A => (try now apply nax);
         rewrite <- (app_nil_l l2); rewrite app_comm_cons, app_assoc; run_nax
  end.
Ltac auto_nax := rewrite <- (app_nil_l _); run_nax.

(* Apply all (reversible) introduction rules *)
Ltac rev_intros := repeat (repeat apply rimpi; repeat apply rfrli); apply rninj.

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
- assert (closed (tup 0 u)) by rnow idtac.
  specialize X with (S n) (tup 0 u).
  rewrite map_map, (map_ext _ _ (nsubs_fup_com _ _)), <- map_map in X.
  rnow autorewrite with term_db in X.
- rnow specialize X with n u0 then rnow eapply (rexsi (ntsubs n u0 u)).
- rewrite <- (freevars_tup 0) in H.
  clear IH2 ; assert (IH2 := X0 (S n0) (tup 0 u) H) ; simpl in IH2.
  rewrite map_map in IH2 ; rewrite (map_ext _ _ (nsubs_fup_com _ _)) in IH2 ;
    rewrite <- map_map in IH2.
  rnow eapply rexse.
Qed.

Lemma rpsubsz_r {l A x u} : closed u ->
  rprove (map fupz l) (subs x (dvar 0) (fupz A)) -> rprove l (subs x u A).
Proof.
intros Hc pi.
apply (rnpsubs 0 u) in pi; [ | assumption ].
rnow simpl in pi then simpl in pi.
now rewrite map_map, (map_ext _ _ (nsubs_z_fup _)), map_id in pi.
Qed.

Lemma rpsubsz_l {l A x u C} : closed u ->
  rprove (subs x (dvar 0) (fupz A) :: map fupz l) (fupz C) -> rprove (subs x u A :: l) C.
Proof.
intros Hc pi.
apply (rnpsubs 0 u) in pi; [ | assumption ].
rnow simpl in pi then simpl in pi.
now rewrite map_map, (map_ext _ _ (nsubs_z_fup _)), map_id in pi.
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
clear k ; apply rnprove_mutrect ; intros;
  (try assert (IH1 := X k)) ; (try assert (IH2 := X0 k)) ;
  (try (econstructor ; eassumption ; fail)).
- rewrite map_app ; apply nax.
- rnow idtac then rnow apply nfrle.
- clear IH1 ; assert (IH := X (S k)).
  rnow change (dvar 0) with (tup (S k) (dvar 0)) in X.
  rewrite map_map, (map_ext _ _ (fup_fup_com _)), <- map_map in IH.
  now apply rfrli.
- rnow idtac then rnow apply (rexsi (tup k u)).
- clear IH2 ; assert (IH2 := X0 (S k)) ; simpl in IH2.
  rnow change (dvar 0) with (tup (S k) (dvar 0)) in X.
  rewrite map_map, (map_ext _ _ (fup_fup_com _)), <- map_map in IH2.
  rnow apply (rexse x (fup k A)).
Qed.


(** * Normalization *)

Theorem denormalization :
  (forall l A, nprove l A -> prove l A) * (forall l A, rprove l A -> prove l A).
Proof. now apply rnprove_mutrect; intros; try (econstructor; eassumption). Qed.

Lemma weakening :
   (forall l A, nprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> nprove (l1 ++ l0 ++ l2) A)
 * (forall l A, rprove l A -> forall l0 l1 l2, l = l1 ++ l2 -> rprove (l1 ++ l0 ++ l2) A).
Proof.
apply rnprove_mutrect ; intros ; try (econstructor; intuition; intuition ; fail) ; subst.
- enough (forall l l3, l1 ++ A :: l2 = l3 ++ l4 -> nprove (l ++ l3 ++ l0 ++ l4) A)
    as HI by (rewrite <- (app_nil_l (l3 ++ l0 ++ l4)) ; apply HI ; assumption) ; clear.
  induction l1; intros l l3 Heq; destruct l3; inversion Heq; subst; simpl.
  + simpl in Heq; subst; rewrite app_assoc; apply nax.
  + apply nax.
  + simpl in Heq; subst; rewrite app_comm_cons, 2 app_assoc; apply nax.
  + replace (l ++ f :: l3 ++ l0 ++ l4) with ((l ++ f :: nil) ++ l3 ++ l0 ++ l4)
      by (rewrite <- app_assoc ; reflexivity).
    now apply IHl1.
- apply rimpi; rewrite app_comm_cons; intuition.
- apply rfrli; rewrite ? map_app; apply X; rewrite map_app; reflexivity.
- apply (rexse x A).
  + now apply X.
  + rewrite ? map_app, app_comm_cons; apply X0 ; now rewrite map_app.
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
- eapply rexse...
  eapply (IHpi (fupz A1) (fupz B1))...
  + clear - Hsub ; intros D l B Hs pi1 pi2.
    rnow eapply (Hsub D)...
  + rewrite <- (app_nil_l (map fupz l)) ; rewrite app_comm_cons ; rewrite <- (app_nil_l _).
    eapply weakening...
    apply rnpup...
Qed.

Lemma frl_reduction : forall A x l, rprove l (frl x A) ->
  forall u, closed u -> rprove l (subs x u A).
Proof with try eassumption ; try reflexivity.
intros A x l pi.
remember (frl x A) as C ; revert A x HeqC ; induction pi ;
  intros A1 x1 HeqC ; inversion HeqC ; subst ; intros u Hc.
- apply rninj ; eapply nfrle...
- eapply rpsubsz_r in pi...
- eapply rexse...
  rnow simpl in IHpi then rnow (eapply IHpi).
Qed.

Lemma exs_reduction : forall A x l, rprove l (exs x A) ->
(forall D l B, fsize D = fsize A -> rprove (D :: l) B -> rprove l D -> rprove l B) -> 
  forall C, rprove (subs x (dvar 0) (fupz A) :: map fupz l) (fupz C) -> rprove l C.
Proof with try eassumption ; try reflexivity.
intros A x l pi.
remember (exs x A) as A' ; revert A x HeqA' ; induction pi ;
  intros A' x1 HeqA' ; inversion HeqA' ; subst ; intros Hsub C pi2.
- eapply rexse...
- eapply rpsubsz_l in pi2...
  rnow apply (Hsub (subs x1 u A')).
- rnow simpl in IHpi.
  eapply rexse...
  eapply IHpi ; [ reflexivity | | ].
  + clear - Hsub ; intros D l B Hs pi1 pi2.
    rnow eapply (Hsub D)...
  + simpl ; rewrite <- (app_nil_l (subs x _ _ :: _)) ; rewrite app_comm_cons ;
      rewrite <- (app_nil_l (map fupz _)) ; rewrite app_comm_cons.
    eapply weakening...
    apply (rnpup 1) in pi2.
    rnow simpl in pi2 then simpl in pi2.
    rewrite map_map in pi2 ; rewrite (map_ext _ _ (fup_fup_com _)) in pi2 ;
      rewrite <- map_map in pi2...
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
  destruct (Compare_dec.le_lt_dec (fsize (imp A0 B)) (fsize A)).
  + eapply IHm in IH1 ; eapply IHm in IH2...
    eapply imp_reduction...
    simpl in l ; intros D l' B' Heq pi1' pi2'.
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
- eapply rexsi...
  refine (snd (IHm _ _ _ _) _ _ _ pi2 _ _)...
- rewrite <- (app_nil_l _) in pi1.
  assert (pi1' := snd weakening _ _ (snd (rnpup 0) pi1)
                  (subs x (dvar 0) (fupz A0) :: nil) nil _ eq_refl) ; simpl in pi1'.
  rewrite map_app in pi1' ; rewrite app_comm_cons in pi1'.
  revert pi2 pi1' Hpi ; rewrite ? map_app ; simpl ; rewrite app_comm_cons ;
    intros pi2 pi1' Hpi.
  assert (fsize (fupz A) = fsize A) as Hup by (rnow idtac).
  eapply (snd (IHm _ Hpi _ Hup) _ _ _ pi2) in pi1'...
  destruct (Compare_dec.le_lt_dec (fsize (exs x A0)) (fsize A)).
  + eapply (snd (fst (IHm _ Hpi _ eq_refl)) _ _ _ n) in pi1...
    simpl in pi1' ; rewrite <- map_app in pi1'.
    eapply exs_reduction...
    simpl in l ; intros D l' B' Heq pi1'' pi2''.
    rewrite <- (app_nil_l _) in pi1''.
    refine (snd (IHn (fsize D) (S (rsize pi1'')) _ _ _) _ _ _ pi1'' _ pi2'')...
  + eapply rexse.
    * refine (fst (fst (IHm _ _ _ _ )) _ _ _ n _ _ _)...
    * rewrite map_app...
Qed.

Lemma smp_substitution : forall l A B, rprove l A -> rprove (A :: l) B -> rprove l B.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A B pi1 pi2.
rewrite <- (app_nil_l (A :: l)) in pi2 ; rewrite <- (app_nil_l l).
refine (snd (substitution (S (rsize pi2)) _ _ ) _ _ _ pi2 _ _)...
Qed.

Theorem normalization : forall l A, prove l A -> rprove l A.
Proof with try eassumption ; try reflexivity ; try lia.
intros l A pi ; induction pi ;
   try (econstructor ; (idtac + econstructor) ; eassumption).
- eapply imp_reduction...
  clear ; intros ; eapply smp_substitution...
- eapply frl_reduction...
- eapply exs_reduction...
  clear ; intros ; eapply smp_substitution...
Qed.


(** * Free variables in [formula] *)
Fixpoint ffreevars A :=
match A with
| var _ l => flat_map freevars l
| imp B C => ffreevars B ++ ffreevars C
| frl x B => remove eq_dt_dec x (ffreevars B)
| exs x B => remove eq_dt_dec x (ffreevars B)
end.

Lemma in_ffreevars_frl : forall x y, y <> x -> forall A,
  In x (ffreevars A) -> In x (ffreevars (frl y A)).
Proof. formula_induction A; apply notin_remove; intuition; now rewrite <- flat_map_concat_map. Qed.

Lemma ffreevars_fup : forall k A, ffreevars (fup k A) = ffreevars A.
Proof. formula_induction A. Qed.
Hint Rewrite ffreevars_fup : term_db.

Lemma nfree_subs : forall x u A, ~ In x (ffreevars A) -> subs x u A = A.
Proof. formula_induction A; try rcauto.
- rnow apply nfree_tsubs then apply H.
- rnow apply H.
- rnow rewrite IHA.
  now apply H; apply in_ffreevars_frl.
- rnow rewrite IHA.
  now apply H; apply in_ffreevars_frl.
Qed.
Hint Rewrite nfree_subs using intuition ; fail : term_db.


(** * Sub-Formula Property *)

(** Sub-formula Relation *)
Inductive subform : formula -> formula -> Prop :=
| sub_id : forall A, subform A A
| sub_imp_l : forall A B C, subform A B -> subform A (imp B C)
| sub_imp_r : forall A B C, subform A B -> subform A (imp C B)
| sub_frl : forall A x u B, subform A (subs x u B) -> subform A (frl x B)
| sub_ex : forall A x u B, subform A (subs x u B) -> subform A (exs x B)
| sub_frl_n : forall A x B, subform A (subs x (dvar 0) (fupz B)) -> subform A (frl x B)
| sub_ex_n : forall A x B, subform A (subs x (dvar 0) (fupz B)) -> subform A (exs x B)
| sub_fup : forall A B, subform A (fupz B) -> subform A B.

Lemma subform_trans : forall A B C, subform A B -> subform B C -> subform A C.
Proof.
now intros A B C Hl Hr; revert A Hl; induction Hr; intros A' Hl; try (econstructor; apply IHHr).
Qed.

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

Lemma rnprove_stronger : forall (P Q : _ -> Prop), (forall x, P x -> Q x) ->
   (forall l A (pi : nprove l A), nprove_with_prop P pi -> nprove_with_prop Q pi)
 * (forall l A (pi : rprove l A), rprove_with_prop P pi -> rprove_with_prop Q pi).
Proof. intros; apply rnprove_mutrect ; simpl ; intuition; eapply Forall_impl ; eassumption. Qed.

Theorem subformula_prop :
   (forall l A (pi : nprove l A), Exists (subform A) l
                               /\ nprove_with_prop (fun B => Exists (subform B) (A :: l)) pi)
 * (forall l A (pi : rprove l A), rprove_with_prop (fun B => Exists (subform B) (A :: l)) pi).
Proof.
apply rnprove_mutrect; simpl.
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









(** * More Lemmas *)

Lemma ffreevars_subs_closed : forall x u, closed u -> forall A,
  ffreevars (subs x u A) = remove eq_dt_dec x (ffreevars A).
Proof. formula_induction A ; rewrite ? remove_app; try now f_equal.
- now f_equal; apply freevars_tsubs_closed.
- case_analysis.
  + symmetry; apply remove_remove_eq.
  + now rewrite remove_remove_neq by (now intros Heq'; apply Heq); f_equal.
- case_analysis.
  + symmetry; apply remove_remove_eq.
  + now rewrite remove_remove_neq by (now intros Heq'; apply Heq); f_equal.
Qed.
Hint Rewrite ffreevars_subs_closed using intuition; fail : term_db.

Lemma ffreevars_subs : forall x y u A, In x (ffreevars (subs y u A)) ->
  (In x (freevars u) /\ In y (ffreevars A)) \/ (In x (ffreevars A) /\ x <> y).
Proof. formula_induction A; try in_solve.
- revert H; induction l; simpl; intros Hin.
  + inversion Hin.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    * apply freevars_tsubs in Hin; in_solve.
    * apply IHl in Hin; in_solve.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  revert H; case_analysis; intros H.
  + right; intuition.
    apply in_remove in H; intuition.
  + assert (Hin := proj1 (in_remove _ _ _ _ H)).
    apply IHA in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition;
      apply notin_remove; intuition.
    subst; revert H; apply remove_In.
Qed.

Lemma subs_subs_eq : forall x u v A, subs x u (subs x v A) = subs x (tsubs x u v) A.
Proof. formula_induction A. Qed.
Hint Rewrite subs_subs_eq : term_db.

Lemma subs_subs_com_closed : forall x v y u, x <> y -> closed u -> closed v ->
  forall A, subs y u (subs x v A) = subs x (tsubs y u v) (subs y u A).
Proof. formula_induction A. Qed.
Hint Rewrite subs_subs_com_closed using intuition; fail : term_db.

Fixpoint good_for x y A :=
match A with
| var X l => True
| imp B C => good_for x y B /\ good_for x y C
| frl z B => In x (ffreevars (frl z B)) -> good_for x y B /\ y <> z
| exs z B => In x (ffreevars (exs z B)) -> good_for x y B /\ y <> z
end.

Lemma good_for_subs : forall x y z t A, closed t -> x <> z ->
  good_for x y A -> good_for x y (subs z t A).
Proof. intros x y z t A; revert t; formula_induction A.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  assert (incl (remove eq_dt_dec x0 (ffreevars (subs z t A))) (remove eq_dt_dec x0 (ffreevars A)))
    as Hincl.
  { apply remove_incl.
    intros a Ha.
    apply ffreevars_subs in Ha; destruct Ha as [Ha|Ha]; intuition.
    exfalso; now rewrite H in H3. }
  revert H1 H2; repeat case_analysis; intros H1 H2; intuition.
  + apply IHA; intuition.
    apply H1; intuition.
  + apply H1; intuition.
Qed.

Lemma subs_subs_com_good : forall x v y u, x <> y -> closed u -> forall A,
  Forall (fun y => good_for x y A) (freevars v) ->
  subs y u (subs x v A) = subs x (tsubs y u v) (subs y u A).
Proof. induction A; simpl; intros Hb; f_equal.
- rnow rewrite 2 map_map; apply map_ext; rcauto.
- apply IHA1; eapply Forall_impl; [ | eassumption ]; simpl; intuition.
- apply IHA2; eapply Forall_impl; [ | eassumption ]; simpl; intuition.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  repeat case_analysis; intuition.
  + destruct (in_dec eq_dt_dec y (freevars v));
     [ destruct (in_dec eq_dt_dec x (ffreevars A)) | ]; rcauto.
    exfalso.
    specialize_Forall Hb with y; apply Hb; intuition.
    now apply notin_remove.
  + destruct (in_dec eq_dt_dec x (ffreevars A)).
    * apply IHA.
      apply Forall_forall; intros z Hinz.
      specialize_Forall Hb with z; apply Hb.
      apply notin_remove; intuition.
    * rewrite 2 (nfree_subs x); [ reflexivity | | assumption ].
      intros Hin; apply n.
      rewrite ffreevars_subs_closed in Hin; [ | assumption ].
      now apply in_remove in Hin.
Qed.
Hint Rewrite subs_subs_com_good using intuition; fail : term_db.

Lemma ffreevars_to_subs : forall A x y t, good_for y x A ->
  In y (ffreevars A) -> In x (freevars t) -> In x (ffreevars (subs y t A)).
Proof. formula_induction A; try in_solve.
- revert H0 H1; clear; induction l; intros Hin1 Hin2; simpl; intuition.
  simpl in Hin1.
  apply in_or_app; apply in_app_or in Hin1; destruct Hin1 as [Hin1|Hin1]; [left|right]; rcauto.
  now apply freevars_to_tsubs.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  apply in_remove in H0; destruct H0 as [Hin Hneq].
  case_analysis; intuition.
  assert (Hin2 := notin_remove eq_dt_dec _ _ x Hneq Hin).
  apply notin_remove; intuition.
Qed.

(* Iterated substitution *)

Fixpoint remove_snd {T} x (L : list (vatom * T)) :=
match L with
| nil => nil
| (y, F) :: TL => if eqb x y then remove_snd x TL else (y, F) :: remove_snd x TL
end.

Lemma remove_snd_remove {T} x (L : list (vatom * T)) :
  remove eq_dt_dec x (map fst L) = map fst (remove_snd x L).
Proof.
induction L; simpl; [ reflexivity | rewrite IHL ]; destruct a; simpl.
repeat case_analysis; intuition.
Qed.
Hint Rewrite (@remove_snd_remove formula) : term_db.

(* iterated substitution *)
Definition multi_subs L A := fold_left (fun F p => subs (fst p) (snd p) F) L A.

Lemma multi_subs_nil : multi_subs nil = id.
Proof. reflexivity. Qed.
Hint Rewrite multi_subs_nil : term_db.

Lemma multi_subs_var : forall L X l, multi_subs L (var X l) = var X (map (multi_tsubs L) l).
Proof.
induction L; intros X l; simpl.
- now rewrite multi_tsubs_nil, map_id.
- now rewrite IHL, map_map.
Qed.
Hint Rewrite multi_subs_var : term_db.

Lemma multi_subs_imp : forall L A B, multi_subs L (imp A B) = imp (multi_subs L A) (multi_subs L B).
Proof. now induction L; intros A B; simpl; [ | rewrite IHL ]. Qed.
Hint Rewrite multi_subs_imp : term_db.

Lemma multi_subs_frl : forall L x A, multi_subs L (frl x A) = frl x (multi_subs (remove_snd x L) A).
Proof.
induction L; intros x A; simpl; [ reflexivity | destruct a; simpl ].
case_analysis; rewrite IHL; f_equal.
Qed.
Hint Rewrite multi_subs_frl : term_db.

Lemma multi_subs_exs : forall L x A, multi_subs L (exs x A) = exs x (multi_subs (remove_snd x L) A).
Proof.
induction L; intros x A; simpl; [ reflexivity | destruct a; simpl ].
case_analysis; rewrite IHL; f_equal.
Qed.
Hint Rewrite multi_subs_exs : term_db.

Lemma multi_subs_closed : forall L A, ffreevars A = nil -> multi_subs L A = A.
Proof.
induction L; intros A Hc; [ reflexivity | destruct a; simpl ].
(rnow rewrite nfree_subs); rewrite Hc in H; inversion H.
Qed.
Hint Rewrite multi_subs_closed using intuition; fail : term_db.

Lemma multi_subs_is_closed : forall L A,
  Forall (fun z => closed z) (map snd L) -> incl (ffreevars A) (map fst L) ->
  ffreevars (multi_subs L A) = nil.
Proof.
induction L; simpl; intros A Hc Hf.
- now apply incl_nil in Hf; subst.
- destruct a; simpl; simpl in Hc, Hf; inversion_clear Hc as [ | ? ? Hc2 HcF].
  apply IHL; intuition.
  intros z Hinz.
  rewrite ffreevars_subs_closed in Hinz by assumption.
  apply in_remove in Hinz; destruct Hinz as [Hinz Hneq].
  apply Hf in Hinz; inversion Hinz; [ exfalso | ]; intuition.
Qed.

Lemma multi_subs_ffreevars : forall L x A, 
  Forall (fun z => closed z) (map snd L) ->
  In x (ffreevars (multi_subs L A)) -> In x (ffreevars A).
Proof.
induction L; intros x A Hc Hin; [ assumption | destruct a; simpl in Hc, Hin ].
inversion_clear Hc as [ | ? ? Hct HcF ].
apply IHL in Hin; trivial.
apply ffreevars_subs in Hin; destruct Hin as [[Hin _]| ]; intuition.
exfalso; rewrite Hct in Hin; inversion Hin.
Qed.

Lemma multi_subs_subs : forall L x v,
  Forall (fun z => closed z) (map snd L) ->
  forall A, Forall (fun y => good_for x y A) (freevars v) ->
  multi_subs L (subs x v A) = subs x (multi_tsubs L v) (multi_subs (remove_snd x L) A).
Proof.
induction L; simpl; intros x v Hc A Hb; [ reflexivity | destruct a; simpl; simpl in Hc ].
inversion_clear Hc as [ | ? ? Hct HcF ].
case_analysis; rewrite <- IHL; intuition; f_equal; rcauto.
- apply Forall_incl with (freevars v); intuition.
  apply incl_remove.
- apply Forall_incl with (freevars v).
  + apply incl_remove.
  + apply Forall_impl with (fun y => good_for x y A); trivial.
    intros a; now apply good_for_subs.
Qed.
Hint Rewrite multi_subs_subs using intuition; fail : term_db.

Lemma multi_subs_remove : forall L A x,
  Forall (fun z => closed z) (map snd L) ->
  ~ In x (ffreevars A) -> multi_subs (remove_snd x L) A = multi_subs L A.
Proof.
induction L; simpl; intros A x Hc Hin; [ reflexivity | destruct a; simpl; simpl in Hc ].
inversion_clear Hc as [ | ? ? Hct HcF ].
case_analysis; rcauto.
apply IHL; try assumption.
intros Hin2; apply Hin.
apply ffreevars_subs in Hin2.
destruct Hin2 as [[Hin2 _]|[Hin2 _]]; trivial.
exfalso; rewrite Hct in Hin2; inversion Hin2.
Qed.
Hint Rewrite multi_subs_remove using intuition; fail : term_db.

Lemma fup_multi_subs : forall L k A,
  fup k (multi_subs L A) = multi_subs (map (fun x => (fst x, tup k (snd x))) L) (fup k A).
Proof. induction L; simpl; intros k A; [ | rewrite IHL ]; rcauto. Qed.
Hint Rewrite fup_multi_subs : term_db.

Lemma multi_subs_ext : forall L A,
  Forall (fun z => closed z) (map snd L) -> incl (ffreevars A) (map fst L) ->
  forall L', multi_subs L A = multi_subs (L ++ L') A.
Proof.
intros L A Hcl Hsub L'.
unfold multi_subs at 2; rewrite fold_left_app.
rewrite multi_subs_closed
  with (A:= fold_left (fun F p => subs (fst p) (snd p) F) L A); trivial.
now apply multi_subs_is_closed.
Qed.

(* All variables occurring (free or bound or for quantification) in a formula *)
Fixpoint allvars A :=
match A with
| var _ l => flat_map freevars l
| imp B C => allvars B ++ allvars C
| frl x B => x :: allvars B
| exs x B => x :: allvars B
end.

Lemma ffreevars_allvars : forall A, incl (ffreevars A) (allvars A).
Proof. formula_induction A.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  eapply incl_tran; [ apply incl_remove | ].
  eapply incl_tran; [ apply IHA | intuition ].
Qed.

Lemma bisubs : forall x y A, ~ In x (allvars A) ->
  subs x (tvar y) (subs y (tvar x) A) = A.
Proof. formula_induction A; f_equal.
- apply tbisubs.
  intros Hin; apply H; simpl; intuition.
- apply H; simpl; intuition.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  repeat case_analysis; intuition.
  apply nfree_subs.
  intros Hin; apply H1.
  now apply ffreevars_allvars.
Qed.


(** * Examples *)
Section Examples.

Variable x y : vatom.

Goal forall A, rprove nil (imp (frl x (frl y A)) (frl y (frl x A))).
Proof.
intros; apply rimpi; repeat (apply rfrli; simpl).
case_analysis; rev_intros.
- rnow apply nfrle.
  replace (frl y (fupz (fupz A)))
     with (subs y (dvar 0) (frl y (fupz (fupz A))))
    by rcauto.
  rnow apply nfrle then subst; rcauto.
- rewrite fup_subs_com, subs_subs_com_closed; intuition.
  rnow apply nfrle.
  replace (frl y (subs x (dvar 0) (fupz (fupz A))))
    with (subs x (dvar 0) (frl y (fupz (fupz A))))
    by (simpl; case_analysis; intuition).
  rnow apply nfrle.
Qed.

Variable f : tatom.
Variable P : fatom.

Goal rprove nil (imp (frl x (var P (tconstr f (tvar x :: nil) :: nil)))
                     (frl x (var P (tconstr f (tconstr f (tvar x :: nil) :: nil) :: nil)))).
Proof.
intros ; rev_intros ; rnow idtac.
case_analysis; intuition.
replace (var P (tconstr f (tconstr f (dvar 0 :: nil) :: nil) :: nil))
   with (subs x (tconstr f (dvar 0 :: nil)) (var P (tconstr f (tvar x :: nil) :: nil)))
  by (simpl; case_analysis; intuition).
rnow apply nfrle.
Qed.

End Examples.


(** ** Hilbert style properties *)

Lemma frl_elim : forall A u x, closed u -> rprove (frl x A :: nil) (subs x u A).
Proof. intros A u x Hf; rev_intros; rnow apply (nfrle u). Qed.

Lemma frl_imp : forall A B x, rprove (frl x (imp A B) :: nil) (imp (frl x A) (frl x B)).
Proof. intros A B x; rev_intros.
apply (nimpe (subs x (dvar 0) (fupz A))).
- change (imp (subs x (dvar 0) (fupz A)) (subs x (dvar 0) (fupz B)))
    with (subs x (dvar 0) (imp (fupz A) (fupz B))).
  apply nfrle ; [ reflexivity | ] ; simpl.
  auto_nax.
- now apply rninj, nfrle, nax_hd.
Qed.

Lemma frl_nfree : forall A x, ~ In x (ffreevars A) -> rprove (A :: nil) (frl x A).
Proof. intros A x Hnf; rev_intros; rnow rewrite nfree_subs. Qed.

Lemma Kcombi : forall A B, rprove nil (imp A (imp B A)).
Proof. intros ; rev_intros; auto_nax. Qed.

Lemma Scombi : forall A B C, rprove nil (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).
Proof with auto with term_db.
intros ; rev_intros.
apply (nimpe B).
- apply (nimpe A)...
  auto_nax.
- apply rninj ; apply (nimpe A)...
  auto_nax.
Qed.

End Formulas.

