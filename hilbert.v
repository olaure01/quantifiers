(* Hilbert system for Intuitionistic Logic with implication *)

Require Import PeanoNat.
Require Import List.






(* TODO move *)

Lemma Forall_fold_right {A} : forall P (l : list A),
  Forall P l <-> fold_right (fun x Q => and (P x) Q) True l.
Proof.
induction l; simpl; split; intros H.
- constructor.
- constructor.
- inversion H as [ | ? ? Ha Hl ]; subst; apply IHl in Hl; now split.
- destruct H as [Ha Hl]; apply IHl in Hl; now constructor.
Qed.

Lemma Exists_fold_right {A} : forall P (l : list A),
  Exists P l <-> fold_right (fun x Q => or (P x) Q) False l.
Proof.
induction l; simpl; split; intros H.
- inversion H.
- inversion H.
- inversion H as [ ? ? Ha | ? ? Hl ]; subst.
  + now left.
  + apply IHl in Hl; now right.
- destruct H as [Ha | Hl]; [ | apply IHl in Hl]; now constructor.
Qed.

Lemma Forall_and {A} : forall (P Q : A -> Prop) l,
  Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
Proof. induction l; intros HP HQ; constructor; inversion HP; inversion HQ; auto. Qed.

Lemma Forall_and_inv {A} : forall (P Q : A -> Prop) l,
  Forall (fun x => P x /\ Q x) l -> Forall P l /\ Forall Q l.
Proof. induction l; intro Hl; split; constructor; inversion Hl; firstorder. Qed.

Lemma Forall_app_inv {A} : forall P (l1 : list A) l2,
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof with try assumption.
induction l1 ; intros.
- split...
  constructor.
- inversion H ; subst.
  apply IHl1 in H3.
  destruct H3.
  split...
  constructor...
Qed.

Lemma Forall_app {A} : forall P (l1 : list A) l2,
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof with try assumption.
induction l1 ; intros...
inversion H ; subst.
apply IHl1 in H0...
constructor...
Qed.

Lemma Exists_app {A} : forall (P : A -> Prop) l1 l2,
  (Exists P l1 \/ Exists P l2) -> Exists P (l1 ++ l2).
Proof with try assumption.
induction l1 ; intros...
- destruct H...
  inversion H.
- destruct H.
  + inversion H ; subst.
    * apply Exists_cons_hd...
    * apply Exists_cons_tl.
      apply IHl1.
      left...
  + apply Exists_cons_tl.
    apply IHl1.
    right...
Qed.

Lemma map_ext_Forall {A B} : forall (f g : A -> B) l,
  Forall (fun x => f x = g x) l -> map f l = map g l.
Proof.
intros ; apply map_ext_in ; apply Forall_forall ; assumption.
Qed.


Lemma remove_cons {T} : forall Hdec l (x : T), remove Hdec x (x :: l) = remove Hdec x l.
Proof. induction l; simpl; intros x; destruct (Hdec x x); try reflexivity; now exfalso. Qed.

Lemma remove_app {T} : forall Hdec l1 l2 (x : T),
  remove Hdec x (l1 ++ l2) = remove Hdec x l1 ++ remove Hdec x l2.
Proof.
induction l1; intros l2 x; simpl.
- reflexivity.
- destruct (Hdec x a).
  + apply IHl1.
  + rewrite <- app_comm_cons; f_equal.
    apply IHl1.
Qed.

Lemma remove_remove_eq {T} : forall Hdec l (x : T), remove Hdec x (remove Hdec x l) = remove Hdec x l.
Proof.
induction l; simpl; intros x; [ reflexivity | ].
destruct (Hdec x a).
- apply IHl.
- simpl; destruct (Hdec x a).
  + now exfalso.
  + now rewrite IHl.
Qed.

Lemma remove_remove_neq {T} : forall Hdec l (x y: T), x <> y ->
  remove Hdec x (remove Hdec y l) = remove Hdec y (remove Hdec x l).
Proof.
induction l; simpl; intros x y Hneq; [ reflexivity | ].
destruct (Hdec y a); simpl; destruct (Hdec x a); subst.
- now apply IHl.
- rewrite remove_cons; now apply IHl.
- now apply IHl.
- simpl; destruct (Hdec y a).
  + now exfalso.
  + now rewrite IHl.
Qed.

Lemma in_remove {T} : forall Hdec l (x y : T), In x (remove Hdec y l) -> In x l /\ x <> y.
Proof.
induction l; intros x y Hin.
- inversion Hin.
- simpl in Hin.
  destruct (Hdec y a); subst; split.
  + right; now apply IHl with a.
  + intros Heq; revert Hin; subst; apply remove_In.
  + inversion Hin; subst; [left; reflexivity|right].
    now apply IHl with y.
  + inversion Hin; subst.
    * now intros Heq; apply n.
    * intros Heq; revert H; subst; apply remove_In.
Qed.

Lemma notin_remove {T} : forall Hdec l (x y : T), x <> y -> In x l -> In x (remove Hdec y l).
Proof.
induction l; simpl; intros x y Hneq Hin.
- inversion Hin.
- destruct (Hdec y a); subst.
  + destruct Hin.
    * exfalso; now apply Hneq.
    * now apply IHl.
  + simpl; destruct Hin; [now left|right].
    now apply IHl.
Qed.

Lemma incl_nil {T} : forall (l : list T), incl l nil -> l = nil.
Proof. now induction l; intros Hincl; [ | exfalso; apply Hincl with a; constructor ]. Qed.

Lemma concat_is_nil {T} : forall (L : list (list T)), concat L = nil <-> Forall (fun x => x = nil) L.
Proof.
induction L; simpl; split; intros Hc; try constructor.
- now apply app_eq_nil in Hc.
- apply IHL; now apply app_eq_nil in Hc.
- inversion Hc; subst; simpl.
  now apply IHL.
Qed.








Require Import fot nj1.



(** * First-Order Terms *)

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
Inductive hterm :=
| hvar : fot.vatom -> hterm
| hconstr : fot.tatom -> list hterm -> hterm.

(** appropriate induction for [term] (with list inside): so called "nested fix" *)
Fixpoint hterm_ind_list_Forall t :
  forall P : hterm -> Prop,
  (forall x, P (hvar x)) ->
  (forall f l, Forall P l -> P (hconstr f l)) -> P t :=
fun P Phvar Pconstr =>
match t with
| hvar x => Phvar x
| hconstr c l => Pconstr c l
    ((fix l_ind l' : Forall P l' :=
      match l' with
      | nil => Forall_nil P
      | cons t1 l1 => Forall_cons _
                        (hterm_ind_list_Forall t1 P Phvar Pconstr)
                        (l_ind l1)
      end) l)
end.
Ltac hterm_induction t :=
  (try intros until t) ;
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  apply (hterm_ind_list_Forall t) ;
  [ intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ;
    repeat (rewrite flat_map_concat_map) ; repeat (rewrite map_map) ;
    try f_equal ; try (apply map_ext_in ; apply Forall_forall) ; try assumption ] ;
  try ((rnow idtac) ; fail); try (rcauto ; fail).


(** * Term substitutions *)

(** substitutes [term] [u] for variable [x] in [term] [t] *)
Fixpoint htsubs x u t :=
match t with
| hvar y => if (fot.beq_vat y x) then u else hvar y
| hconstr c l => hconstr c (map (htsubs x u) l)
end.


(** ** Free variables *)

Fixpoint hfreevars t :=
match t with
| hvar x => x :: nil
| hconstr f l => flat_map hfreevars l
end.
Notation hclosed t := (hfreevars t = nil).

Lemma hclosed_nohfreevars : forall t x, hclosed t -> ~ In x (hfreevars t).
Proof. intros t x Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve hclosed_nohfreevars : term_db.

Lemma nfree_htsubs : forall x u t, ~ In x (hfreevars t) -> htsubs x u t = t.
Proof. hterm_induction t; try rcauto.
- exfalso.
  apply H1.
  now apply beq_eq_vat.
- intros Hin.
  f_equal ; revert IHl Hin ; induction l ; intros; [ reflexivity | ].
  inversion IHl0 ; subst.
  simpl in Hin; simpl; rewrite H1; [ f_equal | ].
  + apply IHl; [ assumption | ].
    intros Hf; apply Hin, in_or_app; now right.
  + intros Hf; apply Hin, in_or_app; now left.
Qed.
Hint Rewrite nfree_htsubs using try (intuition ; fail) ;
                               (try apply hclosed_nohfreevars) ; intuition ; fail : term_db.

Lemma htsubs_htsubs_com : forall x v y u, beq_vat x y = false -> ~ In x (hfreevars u) -> forall t,
  htsubs y u (htsubs x v t) = htsubs x (htsubs y u v) (htsubs y u t).
Proof. hterm_induction t.
rnow case_eq (beq_vat x0 x) ; case_eq (beq_vat x0 y) then try rewrite H1 ; try rewrite H2.
exfalso.
now rewrite eqb_neq in H ; rewrite beq_eq_vat in H1 ; rewrite beq_eq_vat in H2 ; subst.
Qed.
Hint Rewrite htsubs_htsubs_com using try (intuition ; fail) ;
                                    (try apply hclosed_nohfreevars) ; intuition ; fail : term_db.



(* Formulas *)

(** formulas *)
(** first-order formulas in the langage: implication, universal quantification *)
Inductive hformula :=
| hfvar : nj1.atom -> list hterm -> hformula
| himp : hformula -> hformula -> hformula
| hfrl : fot.vatom -> hformula -> hformula
| hexs : fot.vatom -> hformula -> hformula.

Infix "⟶" := himp (at level 70, right associativity).

Ltac hformula_induction A :=
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

Fixpoint hfsize A :=
match A with
| hfvar _ _ => 1
| himp B C => S (hfsize B + hfsize C)
| hfrl _ B => S (hfsize B)
| hexs _ B => S (hfsize B)
end.

Fixpoint hffreevars A :=
match A with
| hfvar _ l => concat (map hfreevars l)
| himp B C => (hffreevars B) ++ (hffreevars C)
| hfrl x B => remove vatomEq.eq_dec x (hffreevars B)
| hexs x B => remove vatomEq.eq_dec x (hffreevars B)
end.

Fixpoint hgood_for x y A :=
match A with
| hfvar X l => True
| himp B C => hgood_for x y B /\ hgood_for x y C
| hfrl z B => In x (hffreevars (hfrl z B)) -> (hgood_for x y B /\ y <> z)
| hexs z B => In x (hffreevars (hexs z B)) -> (hgood_for x y B /\ y <> z)
end.

(** substitutes [hterm] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint hfsubs x u A :=
match A with
| hfvar X l => hfvar X (map (htsubs x u) l)
| himp B C => himp (hfsubs x u B) (hfsubs x u C)
| hfrl y B as C => if (beq_vat y x) then C else hfrl y (hfsubs x u B)
| hexs y B as C => if (beq_vat y x) then C else hexs y (hfsubs x u B)
end.

Lemma hfsize_subs : forall u x A, hfsize (hfsubs x u A) = hfsize A.
Proof. hformula_induction A. Qed.
Hint Rewrite hfsize_subs : term_db.

Inductive hprove : hformula -> Type :=
| hprove_K : forall A B, hprove (A ⟶ B ⟶ A)
| hprove_S : forall A B C, hprove ((A ⟶ B ⟶ C) ⟶ ((A ⟶ B) ⟶ A ⟶ C))
| hprove_MP : forall A B, hprove (A ⟶ B) -> hprove A -> hprove B
| hprove_INST : forall x A t, Forall (fun y => hgood_for x y A) (hfreevars t) ->
                   hprove (hfrl x A ⟶ hfsubs x t A)
| hprove_FRL : forall x A B, ~ In x (hffreevars A) -> hprove ((hfrl x (A ⟶ B)) ⟶ A ⟶ hfrl x B)
| hprove_GEN : forall x A, hprove A -> hprove (hfrl x A)
| hprove_EINST : forall x A t, Forall (fun y => hgood_for x y A) (hfreevars t) ->
                   hprove (hfsubs x t A ⟶ hexs x A)
| hprove_EXS : forall x A B, ~ In x (hffreevars B) -> hprove (hfrl x (A ⟶ B) ⟶ hexs x A ⟶ B).

Lemma hprove_I : forall A, hprove (A ⟶ A).
Proof.
intros A.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K with (B := A ⟶ A).
- apply hprove_K.
Qed.

Lemma hprove_B : forall A B C, hprove ((B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶ C).
Proof.
intros A B C.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + eapply hprove_MP.
    * apply hprove_K.
    * apply hprove_S.
- apply hprove_K.
Qed.

Lemma hprove_C : forall A B C, hprove ((A ⟶ B ⟶ C) ⟶ B ⟶ A ⟶ C).
Proof.
intros A B C.
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

Lemma hprove_W : forall A B, hprove ((A ⟶ A ⟶ B) ⟶ A ⟶ B).
Proof.
intros A B.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_S.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K.
Qed.

Lemma hprove_CUT : forall B A C, hprove (A ⟶ B) -> hprove (B ⟶ C) -> hprove (A ⟶ C).
Proof.
intros B A C pi1 pi2.
eapply hprove_MP; [ eapply hprove_MP | ]; [ apply hprove_B | eassumption | assumption ].
Qed.

Lemma hprove_B2 : forall A B C, hprove ((A ⟶ B) ⟶ (B ⟶ C) ⟶ A ⟶ C).
Proof. intros A B C; eapply hprove_MP; [ apply hprove_C | apply hprove_B ]. Qed.




Lemma tsubs_tsubs_eq : forall x u v t, tsubs x u (tsubs x v t) = tsubs x (tsubs x u v) t.
Proof. term_induction t; now case_eq (beq_vat x0 x); simpl; intros Heq; [ | rewrite Heq ]. Qed.

Lemma freevars_tsubs_closed : forall x u, closed u -> forall t,
  freevars (tsubs x u t) = remove vatomEq.eq_dec x (freevars t).
Proof. term_induction t.
- case_eq (beq_vat x0 x); intros Heq.
  + apply beq_eq_vat in Heq; subst.
    now destruct (vatomEq.eq_dec x x); [ | exfalso; apply n ].
  + apply eqb_neq in Heq.
    destruct (vatomEq.eq_dec x x0).
    * exfalso; now apply Heq.
    * reflexivity.
- revert IHl; induction l; simpl; intros Hl; [ reflexivity | ].
  inversion Hl; subst.
  rewrite IHl; simpl; [ | assumption ].
  now rewrite remove_app; f_equal.
Qed.

Lemma freevars_tsubs : forall x y u t, In x (freevars (tsubs y u t)) -> In x (freevars u) \/ In x (freevars t).
Proof.
term_induction t.
revert IHl; induction l; simpl; intros Hl Hin.
- inversion Hin.
- inversion Hl; subst.
  apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  + apply H1 in Hin.
    destruct Hin as [Hin|Hin]; [left|right]; try assumption.
    now apply in_or_app; left.
  + apply IHl in H2; try assumption.
    destruct H2 as [H2|H2]; [left|right]; try assumption.
    now apply in_or_app; right.
Qed.

Lemma ffreevars_subs_closed : forall x u, closed u -> forall A,
  ffreevars (subs x u A) = remove vatomEq.eq_dec x (ffreevars A).
Proof. formula_induction A; try rewrite remove_app; f_equal; try easy.
- now apply freevars_tsubs_closed.
- case_eq (beq_vat x0 x); intros Heq; simpl.
  + apply beq_eq_vat in Heq; subst.
    symmetry; apply remove_remove_eq.
  + apply eqb_neq in Heq.
    now rewrite remove_remove_neq by (now intros Heq'; apply Heq); f_equal.
- case_eq (beq_vat x0 x); intros Heq; simpl.
  + apply beq_eq_vat in Heq; subst.
    symmetry; apply remove_remove_eq.
  + apply eqb_neq in Heq.
    now rewrite remove_remove_neq by (now intros Heq'; apply Heq); f_equal.
Qed.

Lemma ffreevars_subs : forall x y u A, In x (ffreevars (subs y u A)) -> In x (freevars u) \/ In x (ffreevars A).
Proof.
formula_induction A.
- revert H; induction l; simpl; intros Hin.
  + inversion Hin.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    * apply freevars_tsubs in Hin; destruct Hin as [Hin|Hin].
      -- now left.
      -- right; apply in_or_app; now left.
    * apply IHl in Hin; try assumption.
      destruct Hin as [Hin|Hin]; [left|right]; try assumption.
      now apply in_or_app; right.
- apply in_app_or in H; destruct H as [Hin|Hin].
  + apply A1 in Hin; destruct Hin as [Hin|Hin]; [left|right]; try assumption.
    apply in_or_app; now left.
  + apply IHA1 in Hin; destruct Hin as [Hin|Hin]; [left|right]; try assumption.
    apply in_or_app; now right.
- case_eq (beq_vat x0 y); intros Heq; rewrite Heq in H; simpl in H.
  + now right.
  + assert (Hin := proj1 (in_remove _ _ _ _ H)).
    apply IHA in Hin; destruct Hin as [Hin|Hin]; [now left|right].
    assert (x <> x0) as Hneq
      by (intros Heqx; subst; revert H; apply remove_In).
    remember (ffreevars A) as l; clear - Hneq Hin; induction l.
    * inversion Hin.
    * inversion Hin; subst.
      -- simpl; destruct (vatomEq.eq_dec x0 x); subst.
         ++ exfalso; now apply Hneq.
         ++ now constructor.
      -- simpl; case_eq (vatomEq.eq_dec x0 a); intros e Heq; subst.
         ++ now apply IHl.
         ++ right; now apply IHl.
- case_eq (beq_vat x0 y); intros Heq; rewrite Heq in H; simpl in H.
  + now right.
  + assert (Hin := proj1 (in_remove _ _ _ _ H)).
    apply IHA in Hin; destruct Hin as [Hin|Hin]; [now left|right].
    assert (x <> x0) as Hneq
      by (intros Heqx; subst; revert H; apply remove_In).
    remember (ffreevars A) as l; clear - Hneq Hin; induction l.
    * inversion Hin.
    * inversion Hin; subst.
      -- simpl; destruct (vatomEq.eq_dec x0 x); subst.
         ++ exfalso; now apply Hneq.
         ++ now constructor.
      -- simpl; case_eq (vatomEq.eq_dec x0 a); intros e Heq; subst.
         ++ now apply IHl.
         ++ right; now apply IHl.
Qed.

Lemma ax_hd {l A} : prove (A :: l) A.
Proof. rewrite <- (app_nil_l (A :: l)) ; apply ax. Qed.

Lemma subs_subs_eq : forall x u v A, subs x u (subs x v A) = subs x (tsubs x u v) A.
Proof. formula_induction A.
- apply tsubs_tsubs_eq.
- case_eq (beq_vat x0 x); simpl; intros Heq; rewrite Heq; [ reflexivity | ].
  now rewrite IHA.
- case_eq (beq_vat x0 x); simpl; intros Heq; rewrite Heq; [ reflexivity | ].
  now rewrite IHA.
Qed.

Fixpoint good_for x y A :=
match A with
| var X l => True
| imp B C => good_for x y B /\ good_for x y C
| frl z B => In x (ffreevars (frl z B)) -> (good_for x y B /\ y <> z)
| exs z B => In x (ffreevars (exs z B)) -> (good_for x y B /\ y <> z)
end.

Lemma subs_subs_com_good : forall x v y u, beq_vat x y = false -> closed u ->
  forall A, Forall (fun y => good_for x y A) (freevars v) ->
              subs y u (subs x v A) = subs x (tsubs y u v) (subs y u A).
Proof. induction A; intros Hb.
- simpl ; f_equal ; rnow rewrite 2 map_map ; apply map_ext.
  rnow idtac then rewrite (nfree_tsubs _ _ v) ; try now apply closed_nofreevars.
- simpl in Hb.
  simpl; f_equal.
  + apply IHA1.
    eapply Forall_impl; [ | eassumption ]; simpl.
    intros a [Hba Hba']; apply Hba; now left.
  + apply IHA2.
    eapply Forall_impl; [ | eassumption ]; simpl.
    intros a [Hba Hba']; apply Hba'; now right.
- simpl; case_eq (beq_vat v0 x) ; case_eq (beq_vat v0 y); intros Heq1 Heq2; simpl; rewrite Heq1, Heq2;
    try reflexivity; f_equal.
  + apply beq_eq_vat in Heq1; subst.
    destruct (in_dec vatomEq.eq_dec y (freevars v)); [ destruct (in_dec vatomEq.eq_dec x (ffreevars A)) | ].
    * exfalso.
      apply Forall_forall with (x:=y) in Hb; [ | assumption ].
      simpl in Hb.
      apply (notin_remove vatomEq.eq_dec _ x y) in i0.
      -- now apply Hb in i0.
      -- apply eqb_neq in Heq2.
         intros Heq; now apply Heq2.
    * now rewrite 2 nfree_subs.
    * now rewrite nfree_tsubs; [ reflexivity | ].
  + destruct (in_dec vatomEq.eq_dec x (ffreevars A)).
    * apply IHA.
      apply Forall_forall; intros z Hinz.
      apply Forall_forall with (x:=z) in Hb; [ | assumption ].
      apply Hb.
      simpl; apply notin_remove; [ | assumption ].
      apply eqb_neq in Heq2; intros Heq; now apply Heq2.
    * rewrite 2 (nfree_subs x); [ reflexivity | | assumption ].
      intros Hin; apply n.
      rewrite ffreevars_subs_closed in Hin; [ | assumption ].
      now apply in_remove in Hin.
- simpl; case_eq (beq_vat v0 x) ; case_eq (beq_vat v0 y); intros Heq1 Heq2; simpl; rewrite Heq1, Heq2;
    try reflexivity; f_equal.
  + apply beq_eq_vat in Heq1; subst.
    destruct (in_dec vatomEq.eq_dec y (freevars v)); [ destruct (in_dec vatomEq.eq_dec x (ffreevars A)) | ].
    * exfalso.
      apply Forall_forall with (x:=y) in Hb; [ | assumption ].
      simpl in Hb.
      apply (notin_remove vatomEq.eq_dec _ x y) in i0.
      -- now apply Hb in i0.
      -- apply eqb_neq in Heq2.
         intros Heq; now apply Heq2.
    * now rewrite 2 nfree_subs.
    * now rewrite nfree_tsubs; [ reflexivity | ].
  + destruct (in_dec vatomEq.eq_dec x (ffreevars A)).
    * apply IHA.
      apply Forall_forall; intros z Hinz.
      apply Forall_forall with (x:=z) in Hb; [ | assumption ].
      apply Hb.
      simpl; apply notin_remove; [ | assumption ].
      apply eqb_neq in Heq2; intros Heq; now apply Heq2.
    * rewrite 2 (nfree_subs x); [ reflexivity | | assumption ].
      intros Hin; apply n.
      rewrite ffreevars_subs_closed in Hin; [ | assumption ].
      now apply in_remove in Hin.
Qed.






Lemma nfree_hfsubs : forall x u A, ~ In x (hffreevars A) -> hfsubs x u A = A.
Proof. hformula_induction A; try rcauto.
- apply nfree_htsubs.
  intros  Hin; apply H.
  now apply in_or_app; left.
- apply H.
  now apply in_or_app; right.
- f_equal.
  apply IHA.
  intros Hin; apply H.
  apply eqb_neq in H0.
  apply notin_remove; [ | assumption ].
  intros Heq; now apply H0.
- f_equal.
  apply IHA.
  intros Hin; apply H.
  apply eqb_neq in H0.
  apply notin_remove; [ | assumption ].
  intros Heq; now apply H0.
Qed.

Lemma hfreevars_tsubs_closed : forall x u, hclosed u -> forall t,
  hfreevars (htsubs x u t) = remove vatomEq.eq_dec x (hfreevars t).
Proof. hterm_induction t.
- case_eq (beq_vat x0 x); intros Heq.
  + apply beq_eq_vat in Heq; subst.
    now destruct (vatomEq.eq_dec x x); [ | exfalso; apply n ].
  + apply vatomFacts.eqb_neq in Heq.
    destruct (vatomEq.eq_dec x x0).
    * exfalso; now apply Heq.
    * reflexivity.
- revert IHl; induction l; simpl; intros Hl; [ reflexivity | ].
  inversion Hl; subst.
  rewrite IHl; simpl; [ | assumption ].
  now rewrite remove_app; f_equal.
Qed.

Lemma hfreevars_tsubs : forall x y u t, In x (hfreevars (htsubs y u t)) ->
  (In x (hfreevars u) /\ In y (hfreevars t)) \/ (In x (hfreevars t) /\ x <> y).
Proof.
hterm_induction t; intros Hin.
- case_eq (beq_vat x0 y); intros Heq; rewrite Heq in Hin; auto.
  + apply beq_eq_vat in Heq; auto.
  + simpl in Hin; destruct Hin; auto; subst.
    right; split; auto.
    now apply eqb_neq.
- revert IHl Hin; induction l; simpl; intros Hl Hin.
  + inversion Hin.
  + inversion Hl; subst.
    apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    * apply H1 in Hin.
      destruct Hin as [Hin|Hin]; [left|right].
      -- destruct Hin; split; auto.
         apply in_or_app; auto.
      -- split.
         ++ now apply in_or_app; left.
         ++ destruct Hin; auto.
    * apply IHl in H2; auto.
      destruct H2 as [H2|H2]; [left|right].
      -- destruct H2; split; auto.
         apply in_or_app; auto.
      -- split.
         ++ now apply in_or_app; right.
         ++ destruct H2; auto.
Qed.

Lemma hffreevars_subs : forall x y u A, In x (hffreevars (hfsubs y u A)) ->
  (In x (hfreevars u) /\ In y (hffreevars A)) \/ (In x (hffreevars A) /\ x <> y).
Proof. formula_induction A.
- revert H; induction l; simpl; intros Hin; [ now idtac | ].
  apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  + apply hfreevars_tsubs in Hin; destruct Hin as [Hin|Hin]; [left|right]; destruct Hin; split; auto.
    * now apply in_or_app; left.
    * now apply in_or_app; left.
  + apply IHl in Hin; destruct Hin as [Hin|Hin]; [left|right]; destruct Hin; split; auto.
    * now apply in_or_app; right.
    * now apply in_or_app; right.
- apply in_app_or in H; destruct H as [H|H].
  + apply A1 in H; destruct H as [H|H]; [left|right]; destruct H; split; auto.
    * now apply in_or_app; left.
    * now apply in_or_app; left.
  + apply IHA1 in H; destruct H as [H|H]; [left|right]; destruct H; split; auto.
    * now apply in_or_app; right.
    * now apply in_or_app; right.
- case_eq (beq_vat x0 y); intros Heq; rewrite Heq in H.
  + right.
    apply beq_eq_vat in Heq; subst.
    simpl in H; apply in_remove in H; destruct H; split; auto.
    now apply notin_remove.
  + simpl in H; apply in_remove in H; destruct H as [H Hneq].
    apply IHA in H; destruct H as [H|H]; [left|right]; destruct H; split; auto.
    * apply eqb_neq in Heq.
      apply notin_remove; auto.
    * now apply notin_remove.
- case_eq (beq_vat x0 y); intros Heq; rewrite Heq in H.
  + right.
    apply beq_eq_vat in Heq; subst.
    simpl in H; apply in_remove in H; destruct H; split; auto.
    now apply notin_remove.
  + simpl in H; apply in_remove in H; destruct H as [H Hneq].
    apply IHA in H; destruct H as [H|H]; [left|right]; destruct H; split; auto.
    * apply eqb_neq in Heq.
      apply notin_remove; auto.
    * now apply notin_remove.
Qed.

Lemma hfreevars_to_tsubs : forall t a x u,
  In x (hfreevars t) -> In a (hfreevars u) -> In a (hfreevars (htsubs x u t)).
Proof. hterm_induction t; intros a y u Hin1 Hin2.
- destruct Hin1 as [Hin1|Hin1]; [ | inversion Hin1 ].
  now apply beq_eq_vat in Hin1; rewrite Hin1.
- revert IHl Hin1; induction l; simpl; intros Hl Hin; [ inversion Hin | ].
  inversion Hl; subst.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [ left | right ].
  + now apply H1.
  + now apply IHl.
Qed.

Lemma hffreevars_to_subs : forall A a x t,
  Forall (fun y => hgood_for x y A) (hfreevars t) ->
  In x (hffreevars A) -> In a (hfreevars t) -> In a (hffreevars (hfsubs x t A)).
Proof. hformula_induction A.
- revert H0 H1; clear; induction l; intros Hin1 Hin2; simpl.
  + inversion Hin1.
  + simpl in Hin1.
    apply in_or_app; apply in_app_or in Hin1; destruct Hin1 as [Hin1|Hin1]; [left|right].
    * now apply hfreevars_to_tsubs.
    * now apply IHl.
- apply Forall_and_inv in H; destruct H as [Hl Hr].
  apply in_or_app; apply in_app_or in H0; destruct H0 as [Hin|Hin]; [ left | right ].
  + now apply A1.
  + now apply IHA1.
- case_eq (beq_vat x x0); intros Heq; simpl.
  + exfalso.
    apply beq_eq_vat in Heq; subst.
    now apply remove_In in H0.
  + case_eq (beq_vat a x); intros Heq2.
    * exfalso.
      apply beq_eq_vat in Heq2; subst.
      apply vatomFacts.eqb_neq in Heq.
      apply in_remove in H0.
      apply Forall_forall with (x:=x) in H; [ | assumption ].
      destruct H0.
      apply (notin_remove vatomEq.eq_dec _ x0 x) in H0.
      -- now apply H in H0.
      -- intros Heq2; now apply Heq.
    * apply vatomFacts.eqb_neq in Heq2.
      apply notin_remove; [ assumption | ].
      apply IHA; try assumption.
      -- apply Forall_forall; intros y Hy.
         apply Forall_forall with (x:=y) in H; [ | assumption ].
         now apply H in H0.
      -- apply vatomFacts.eqb_neq in Heq.
         now apply in_remove in H0.
- case_eq (beq_vat x x0); intros Heq; simpl.
  + exfalso.
    apply beq_eq_vat in Heq; subst.
    now apply remove_In in H0.
  + case_eq (beq_vat a x); intros Heq2.
    * exfalso.
      apply beq_eq_vat in Heq2; subst.
      apply vatomFacts.eqb_neq in Heq.
      apply in_remove in H0.
      apply Forall_forall with (x:=x) in H; [ | assumption ].
      destruct H0.
      apply (notin_remove vatomEq.eq_dec _ x0 x) in H0.
      -- now apply H in H0.
      -- intros Heq2; now apply Heq.
    * apply vatomFacts.eqb_neq in Heq2.
      apply notin_remove; [ assumption | ].
      apply IHA; try assumption.
      -- apply Forall_forall; intros y Hy.
         apply Forall_forall with (x:=y) in H; [ | assumption ].
         now apply H in H0.
      -- apply vatomFacts.eqb_neq in Heq.
         now apply in_remove in H0.
Qed.






(* From Hilbert to Natural Deduction *)

Fixpoint h2n_term t :=
match t with
| hvar x => tvar x
| hconstr f l => tconstr f (map h2n_term l)
end.


Lemma h2n_freevars : forall t, freevars (h2n_term t) = hfreevars t.
Proof. hterm_induction t. Qed.

Lemma h2n_closed : forall t, hclosed t <-> closed (h2n_term t).
Proof.
intros t; rewrite h2n_freevars; destruct (hfreevars t); simpl; split; intros Heq; try reflexivity;
  inversion Heq.
Qed.

Lemma h2n_tsubs : forall x u t,
  h2n_term (htsubs x u t) = tsubs x (h2n_term u) (h2n_term t).
Proof. hterm_induction t; rewrite <- beq_hat_vat; now case_eq (beq_hat x0 x); intros Heqb. Qed.

Lemma h2n_tup : forall k t, tup k (h2n_term t) = h2n_term t.
Proof. hterm_induction t. Qed.


Fixpoint h2n_formula A :=
match A with
| hfvar X l => var X (map h2n_term l)
| himp B C => imp (h2n_formula B) (h2n_formula C)
| hfrl y B => frl y (h2n_formula B)
| hexs y B => exs y (h2n_formula B)
end.

Lemma h2n_ffreevars : forall A, ffreevars (h2n_formula A) = hffreevars A.
Proof. hformula_induction A; try rewrite map_app; f_equal; try assumption; apply h2n_freevars. Qed.

Lemma h2n_fclosed : forall A, hffreevars A = nil <-> ffreevars (h2n_formula A) = nil.
Proof.
intros A; rewrite h2n_ffreevars; destruct (hffreevars A); simpl; split; intros Heq; try reflexivity;
  inversion Heq.
Qed.

Lemma h2n_fsubs : forall x u A,
  h2n_formula (hfsubs x u A) = subs x (h2n_term u) (h2n_formula A).
Proof. hformula_induction A.
- apply h2n_tsubs.
- now case_eq (beq_vat x0 x); intros Heqb; simpl; [ | rewrite IHA ].
- now case_eq (beq_vat x0 x); intros Heqb; simpl; [ | rewrite IHA ].
Qed.

Lemma h2n_fup : forall k A, fup k (h2n_formula A) = h2n_formula A.
Proof. hformula_induction A; apply h2n_tup. Qed.

Fixpoint remove_snd {T : Type} x (L : list (vatom * T)) :=
match L with
| nil => nil
| (y, F) :: TL => if beq_vat x y then remove_snd x TL else (y, F) :: remove_snd x TL
end.

Lemma remove_snd_remove {T} x (L : list (vatom * T)) :
  remove vatomEq.eq_dec x (map fst L) = map fst (remove_snd x L).
Proof.
induction L; simpl; [ reflexivity | rewrite IHL ].
destruct a; simpl.
destruct (vatomEq.eq_dec x v); subst.
- now rewrite (proj2 (beq_eq_vat v v) eq_refl).
- now apply eqb_neq in n; rewrite n.
Qed.


Definition multi_tsubs L t :=
  fold_left (fun F p => tsubs (fst p) (snd p) F) L t.

Lemma multi_tsubs_dvar : forall L n, multi_tsubs L (dvar n) = dvar n.
Proof. now induction L; intros n; simpl; [ | rewrite IHL ]. Qed.

Lemma multi_tsubs_nvar : forall L x, ~ In x (map fst L) -> multi_tsubs L (tvar x) = tvar x.
Proof.
induction L; intros x Hin; simpl; [ reflexivity | ].
destruct a; simpl; case_eq (beq_vat x v); intros Heq.
- exfalso.
  apply beq_eq_vat in Heq; subst.
  now apply Hin; left.
- apply IHL.
  now intros Hin2; apply Hin; right.
Qed.

Lemma multi_tsubs_tconstr : forall L f l, multi_tsubs L (tconstr f l) = tconstr f (map (multi_tsubs L) l).
Proof.
induction L; intros f l; simpl.
- f_equal; now induction l; simpl; [ | rewrite <- IHl ].
- rewrite IHL.
  f_equal; rewrite map_map; f_equal.
Qed.

Lemma multi_tsubs_tsubs : forall L x v, ~ In x (map fst L) ->
  Forall (fun z => ~ In x (freevars (snd z))) L ->
  forall t, multi_tsubs L (tsubs x v t) = tsubs x (multi_tsubs L v) (multi_tsubs L t).
Proof. term_induction t.
- now rewrite multi_tsubs_dvar; simpl.
- case_eq (beq_vat x0 x); intros Heq.
  + apply beq_eq_vat in Heq; subst.
    rewrite multi_tsubs_nvar by assumption; simpl.
    now rewrite eqb_refl.
  + rewrite nfree_tsubs; [ reflexivity | ].
    apply eqb_neq in Heq.
   apply Forall_Exists_neg in H0.
   intros Hin; apply H0.
   assert (~ In x (freevars (tvar x0))) as Hu
     by (simpl; intros Hor; apply Heq; now destruct Hor).
   remember (tvar x0) as u.
   clear Hequ; revert u Hin Hu; clear; induction L using rev_ind; simpl; intros u Hin Hterm.
    * exfalso; now apply Hterm.
    * destruct x0; simpl in Hin; simpl.
      unfold multi_tsubs in Hin.
      rewrite fold_left_app in Hin; simpl in Hin.
      apply freevars_tsubs in Hin; destruct Hin as [Hin|Hin].
      -- now apply Exists_app; right; constructor; simpl.
      -- apply Exists_app; left.
         now apply IHL with u.
- rewrite 2 multi_tsubs_tconstr; simpl; f_equal.
  rewrite 2 map_map.
  now apply map_ext_Forall.
Qed.

Lemma multi_tsubs_closed : forall L t, closed t -> multi_tsubs L t = t.
Proof.
induction L; intros t Hc; [ reflexivity | ].
destruct a; simpl.
rewrite nfree_tsubs by now apply closed_nofreevars.
now apply IHL.
Qed.

Lemma multi_tsubs_is_closed : forall L t,
  Forall (fun z : term => closed z) (map snd L) ->
  incl (freevars t) (map (fun z => fst z) L) ->
closed (multi_tsubs L t).
Proof.
induction L; simpl; intros t Hc Hf.
- now apply incl_nil in Hf; subst.
- destruct a; simpl; simpl in Hc, Hf.
  apply IHL.
  + now inversion Hc.
  + intros z Hinz.
    inversion Hc; subst.
    rewrite freevars_tsubs_closed in Hinz by assumption.
    apply in_remove in Hinz; destruct Hinz as [Hinz Hneq].
    apply Hf in Hinz; inversion Hinz.
    * exfalso; now rewrite H in Hneq.
    * assumption.
Qed.


Definition multi_subs L A :=
  fold_left (fun F p => subs (fst p) (snd p) F) L A.

Lemma multi_subs_var : forall L X l, multi_subs L (var X l) = var X (map (multi_tsubs L) l).
Proof.
induction L; intros X l; simpl.
- f_equal; now induction l; simpl; [ | rewrite <- IHl ].
- rewrite IHL.
  f_equal; rewrite map_map; f_equal.
Qed.

Lemma multi_subs_imp : forall L A B, multi_subs L (imp A B) = imp (multi_subs L A) (multi_subs L B).
Proof. now induction L; intros A B; simpl; [ | rewrite IHL ]. Qed.

Lemma multi_subs_frl : forall L x A, multi_subs L (frl x A) = frl x (multi_subs (remove_snd x L) A).
Proof.
induction L; intros x A; simpl; [ reflexivity | destruct a; simpl ].
case_eq (beq_vat x v); intros Heq; rewrite IHL; f_equal.
Qed.

Lemma multi_subs_exs : forall L x A, multi_subs L (exs x A) = exs x (multi_subs (remove_snd x L) A).
Proof.
induction L; intros x A; simpl; [ reflexivity | destruct a; simpl ].
case_eq (beq_vat x v); intros Heq; rewrite IHL; f_equal.
Qed.

Lemma multi_subs_closed : forall L A, ffreevars A = nil -> multi_subs L A = A.
Proof.
induction L; intros A Hc; [ reflexivity | ].
destruct a; simpl.
rewrite nfree_subs by (rewrite Hc; intros Hin; inversion Hin).
now apply IHL.
Qed.

Lemma multi_subs_is_closed : forall L A,
  Forall (fun z : term => closed z) (map snd L) ->
  incl (ffreevars A) (map (fun z => fst z) L) ->
ffreevars (multi_subs L A) = nil.
Proof.
induction L; simpl; intros A Hc Hf.
- now apply incl_nil in Hf; subst.
- destruct a; simpl; simpl in Hc, Hf.
  apply IHL.
  + now inversion Hc.
  + intros z Hinz.
    inversion Hc; subst.
    rewrite ffreevars_subs_closed in Hinz by assumption.
    apply in_remove in Hinz; destruct Hinz as [Hinz Hneq].
    apply Hf in Hinz; inversion Hinz.
    * exfalso; now rewrite H in Hneq.
    * assumption.
Qed.

Lemma multi_subs_ffreevars L x A: 
  Forall (fun z : term => closed z) (map snd L) ->
In x (ffreevars (multi_subs L A)) -> In x (ffreevars A).
Proof.
induction L using rev_ind; simpl; intros Hc Hin; [ assumption | ].
destruct x0; simpl in Hin.
rewrite map_app in Hc; apply Forall_app_inv in Hc; simpl in Hc; destruct Hc as [Hc1 Hc2].
unfold multi_subs in Hin; rewrite fold_left_app in Hin; simpl in Hin.
apply ffreevars_subs in Hin; destruct Hin as [Hin|Hin].
- exfalso.
  inversion Hc2; rewrite H1 in Hin; inversion Hin.
- now apply IHL.
Qed.

Lemma multi_subs_subs : forall L x v,
  Forall (fun z : term => closed z) (map snd L) ->
  forall A, Forall (fun y => good_for x y A) (freevars v) ->
  multi_subs L (subs x v A) = subs x (multi_tsubs L v) (multi_subs (remove_snd x L) A).
Proof.
induction L; simpl; intros x v Hc A Hb; [ reflexivity | ].
destruct a; simpl; simpl in Hc; inversion Hc; subst.
case_eq (beq_vat x v0); simpl; intros Heq; rewrite <- IHL; try assumption.
- rewrite beq_eq_vat in Heq; subst; f_equal.
  apply subs_subs_eq.
- rewrite beq_eq_vat in Heq; subst.
  apply Forall_forall; intros z Hinz.
  apply freevars_tsubs in Hinz.
  destruct Hinz as [Hinz|Hinz].
  { exfalso; rewrite H1 in Hinz; inversion Hinz. }
  now apply Forall_forall with (x := z) in Hb.
- f_equal.
  now rewrite subs_subs_com_good.
- apply Forall_forall; intros z Hinz.
  apply freevars_tsubs in Hinz.
  destruct Hinz as [Hinz|Hinz].
  { exfalso; rewrite H1 in Hinz; inversion Hinz. }
  apply Forall_forall with (x := z) in Hb; [ | assumption ].
  apply eqb_neq in Heq.
  assert (v0 <> x) as Heq2 by (intros Heq2; now apply Heq).
  revert H1 Hb Heq; clear; induction A; simpl; intros Hc Hb Heq.
  + constructor.
  + now destruct Hb as [Hb1 Hb2]; split; [ apply IHA1 | apply IHA2 ].
  + case_eq (beq_vat v v0); intros Heq2; simpl.
    * assumption.
    * enough (In x (ffreevars (subs v0 t A)) -> In x (ffreevars A)) as Himp.
      { intros Hin.
        apply in_remove in Hin; destruct Hin as [Hin Hneq].
        apply Himp in Hin.
        apply notin_remove with vatomEq.eq_dec (ffreevars A) x v in Hin; [ | assumption ].
        apply Hb in Hin.
        split; [ | apply Hin ].
        now apply IHA. }
      intros Hin; apply ffreevars_subs in Hin.
      destruct Hin as [Hin|Hin].
      -- rewrite Hc in Hin; inversion Hin.
      -- assumption.
  + case_eq (beq_vat v v0); intros Heq2; simpl.
    * assumption.
    * enough (In x (ffreevars (subs v0 t A)) -> In x (ffreevars A)) as Himp.
      { intros Hin.
        apply in_remove in Hin; destruct Hin as [Hin Hneq].
        apply Himp in Hin.
        apply notin_remove with vatomEq.eq_dec (ffreevars A) x v in Hin; [ | assumption ].
        apply Hb in Hin.
        split; [ | apply Hin ].
        now apply IHA. }
      intros Hin; apply ffreevars_subs in Hin.
      destruct Hin as [Hin|Hin].
      -- rewrite Hc in Hin; inversion Hin.
      -- assumption.
Qed.

Lemma multi_subs_remove : forall L A x,
  Forall (fun z : term => closed z) (map snd L) ->
  ~ In x (ffreevars A) -> multi_subs (remove_snd x L) A = multi_subs L A.
Proof.
induction L; simpl; intros A x Hc Hin; [ reflexivity | ].
destruct a; simpl; simpl in Hc.
case_eq (beq_vat x v); intros Heq; simpl.
- apply beq_eq_vat in Heq; subst.
  rewrite nfree_subs by assumption.
  inversion Hc; subst; now apply IHL.
- inversion Hc; subst.
  apply IHL; try assumption.
  apply eqb_neq in Heq.
  intros Hin2; apply Hin; clear - Heq H1 Hin2.
  apply ffreevars_subs in Hin2.
  destruct Hin2 as [Hin2|Hin2].
  + exfalso.
    rewrite H1 in Hin2; inversion Hin2.
  + assumption.
Qed.

Lemma fup_multi_subs : forall L k A,
  fup k (multi_subs L A) = multi_subs (map (fun x => (fst x, tup k (snd x))) L) (fup k A).
Proof. now induction L; simpl; intros k A; [ reflexivity | rewrite IHL ]; rewrite fup_subs_com. Qed.

Lemma multi_subs_ext : forall L A,
  Forall (fun z : term => closed z) (map snd L) ->
  incl (hffreevars A) (map fst L) ->
forall L', multi_subs L (h2n_formula A) = multi_subs (L ++ L') (h2n_formula A).
Proof.
intros L A Hcl Hsub L'.
unfold multi_subs at 2; rewrite fold_left_app.
rewrite multi_subs_closed
  with (A:= fold_left (fun (F : formula) (p : vatom * term) => subs (fst p) (snd p) F) L (h2n_formula A)).
- reflexivity.
- apply multi_subs_is_closed; [ assumption | ].
  revert Hsub; clear; induction L; intros Hincl z Hinz.
  + exfalso.
    rewrite h2n_ffreevars in Hinz.
    apply Hincl in Hinz; inversion Hinz.
  + rewrite h2n_ffreevars in Hinz.
    now apply Hincl in Hinz.
Qed.



Proposition h2n : forall A, hprove A ->
  forall L, Forall (fun z => closed z) (map snd L) ->
            incl (hffreevars A) (map fst L) ->
  prove nil (multi_subs L (h2n_formula A)).
Proof.
intros A pi; induction pi; intros L Hcl Hsub;
  simpl; rewrite ? multi_subs_imp;
  remember (multi_subs L (h2n_formula A)) as AA;
  (try remember (multi_subs L (h2n_formula B)) as BB);
  (try remember (multi_subs L (h2n_formula C)) as CC);
  repeat apply impi.
- change (BB :: AA :: nil) with ((BB :: nil) ++ AA :: nil).
  apply ax.
- apply (impe BB).
  + apply (impe AA).
    * change (AA :: imp AA BB :: imp AA (imp BB CC) :: nil)
        with ((AA :: imp AA BB :: nil) ++ imp AA (imp BB CC) :: nil).
      apply ax.
    * apply ax_hd.
  + apply (impe AA).
    * change (AA :: imp AA BB :: imp AA (imp BB CC) :: nil)
        with ((AA :: nil) ++ imp AA BB :: imp AA (imp BB CC) :: nil).
      apply ax.
    * apply ax_hd.
- remember (map (fun x => (x, dvar 0)) (hffreevars A)) as LA.
  remember (multi_subs (L ++ LA) (h2n_formula A)) as AAA.
  apply (impe AAA).
  + specialize IHpi1 with (L ++ LA).
    simpl in IHpi1;rewrite ? multi_subs_imp in IHpi1.
    subst AAA BB; rewrite multi_subs_ext with L B LA; try assumption; apply IHpi1.
    * rewrite map_app; apply Forall_app; [ assumption | subst LA ].
      remember (hffreevars A) as l; clear; induction l; simpl; now constructor.
    * rewrite map_app; apply incl_app; [ apply incl_appr | apply incl_appl ].
      -- subst LA; remember (hffreevars A) as l; clear; induction l; simpl.
         ++ apply incl_refl.
         ++ apply incl_cons; [ | now apply incl_tl ].
            now constructor.
      -- assumption.
  + subst AAA; apply IHpi2.
    * rewrite map_app; apply Forall_app; [ assumption | subst LA ].
      remember (hffreevars A) as l; clear; induction l; simpl; now constructor.
    * rewrite map_app; apply incl_appr.
      subst LA; remember (hffreevars A) as l; clear; induction l; simpl.
      -- apply incl_refl.
      -- apply incl_cons; [ | now apply incl_tl ].
         now constructor.
- rewrite multi_subs_frl.
  rewrite h2n_fsubs.
  rewrite multi_subs_subs; try assumption.
  + destruct (in_dec vatomEq.eq_dec x (ffreevars (h2n_formula A))) as [Hf|Hf].
    * apply frle; [ | apply ax_hd ].
      clear - f Hcl Hsub Hf.
      apply multi_tsubs_is_closed; [ assumption | ].
      intros a Hin.
      unfold incl in Hsub; specialize Hsub with a; simpl in Hsub.
      assert (In a (hffreevars (hfsubs x t A))) as HvA.
      { rewrite h2n_ffreevars in Hf.
        rewrite h2n_freevars in Hin.
        now apply hffreevars_to_subs. }
      now eapply or_intror in HvA; apply in_or_app in HvA; eapply Hsub in HvA.
    * assert (~ In x (ffreevars (multi_subs (remove_snd x L) (h2n_formula A)))) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_ffreevars in Hin; try assumption.
        clear - Hcl; apply Forall_forall; intros a Hin.
        apply Forall_forall with (x:=a) in Hcl; [ assumption | ].
        revert Hin; clear; induction L; simpl; intros Hin.
        - inversion Hin.
        - destruct a0; simpl; simpl in Hin.
          case_eq (beq_vat x v); intros Heq; rewrite Heq in Hin.
          + now right; apply IHL.
          + inversion Hin as [Hin'|Hin']; simpl in Hin'.
            * now left.
            * now right; apply IHL. }
      rewrite nfree_subs by assumption.
      rewrite <- (nfree_subs _ (dvar 0) _ Hnin).
      apply frle; [ reflexivity | ].
      rewrite nfree_subs by assumption.
      apply ax_hd.
  + apply Forall_forall; intros z Hinz.
    apply Forall_forall with (x:=z) in f.
    * revert f; clear; hformula_induction A.
      -- apply IHA.
         apply f.
         now rewrite <- h2n_ffreevars.
      -- apply f; [ | assumption ].
         now rewrite <- h2n_ffreevars.
      -- apply IHA.
         apply f.
         now rewrite <- h2n_ffreevars.
      -- apply f; [ | assumption ].
         now rewrite <- h2n_ffreevars.
    * now rewrite <- h2n_freevars.
- rewrite ? multi_subs_frl.
  rewrite <- multi_subs_remove with (x:=x) in HeqAA; try assumption.
  + apply frli; simpl.
    apply impe with (fupz AA); [ | apply ax_hd ].
    rewrite multi_subs_imp; simpl; rewrite <- HeqAA.
    replace (imp (fupz AA) (subs x (dvar 0)
                                (fupz (multi_subs (remove_snd x L) (h2n_formula B)))))
       with (imp (subs x (dvar 0) (fupz AA))
                           (subs x (dvar 0)
                                 (fupz (multi_subs (remove_snd x L) (h2n_formula B))))).
    2:{ f_equal.
        enough (~ In x (ffreevars (fupz AA))) as Hf by now apply nfree_subs.
        intros Hin; apply n; clear - Hcl HeqAA Hin.
        rewrite ffreevars_fup in Hin; subst.
        apply multi_subs_ffreevars in Hin.
        - now rewrite <- h2n_ffreevars.
        - revert Hcl; clear; induction L; simpl; intros Hcl; [ constructor | ].
          destruct a; simpl; simpl in Hcl; inversion Hcl; subst.
          case_eq (beq_vat x v); intros Heq; simpl.
          + now apply IHL.
          + constructor; auto. }
    change (imp (subs x (dvar 0) (fupz AA))
                (subs x (dvar 0)
                      (fupz (multi_subs (remove_snd x L) (h2n_formula B)))))
      with (subs x (dvar 0) (imp (fupz AA)
                      (fupz (multi_subs (remove_snd x L) (h2n_formula B))))).
    apply frle; [ reflexivity | ].
    change (fupz AA :: frl x
              (imp (fupz AA) (fupz (multi_subs (remove_snd x L) (h2n_formula B)))) :: nil)
      with ((fupz AA :: nil) ++ frl x
              (imp (fupz AA) (fupz (multi_subs (remove_snd x L) (h2n_formula B)))) :: nil).
    apply ax.
  + intros Hin; apply n; clear - Hin.
    now rewrite h2n_ffreevars in Hin.
- rewrite multi_subs_frl.
  apply frli; simpl.
  rewrite fup_multi_subs.
  rewrite h2n_fup.
  replace (subs x (dvar 0)
          (multi_subs (map (fun x0=> (fst x0, tup 0 (snd x0))) (remove_snd x L))
             (h2n_formula A)))
     with (multi_subs ((map (fun x0 => (fst x0, tup 0 (snd x0))) (remove_snd x L) ++
             (x, dvar 0) :: nil)) (h2n_formula A))
    by now unfold multi_subs; rewrite fold_left_app; simpl.
  apply IHpi.
  + rewrite map_app; apply Forall_app.
    * rewrite map_map; simpl.
      revert Hcl; clear; induction L; simpl; intros HF; [ now constructor | ].
      inversion HF; subst.
      destruct a; simpl; simpl in H1.
      case_eq (beq_vat x v); intros Heq; simpl.
      -- now apply IHL.
      -- constructor; [ | now apply IHL ].
         now rewrite freevars_tup.
    * now repeat constructor.
  + clear - Hsub; simpl in Hsub.
    intros a Hin.
    rewrite map_app; apply in_or_app.
    destruct (vatomEq.eq_dec x a); subst; [ right | left ]; simpl.
    * now left.
    * unfold incl in Hsub; specialize Hsub with a.
      apply notin_remove with vatomEq.eq_dec _ _ x in Hin; [ | intros Heq; now apply n ].
      apply Hsub in Hin.
      rewrite map_map; simpl.
      apply notin_remove with vatomEq.eq_dec _ _ x in Hin; [ | intros Heq; now apply n ].
      now rewrite remove_snd_remove in Hin.
- rewrite multi_subs_exs.
  rewrite h2n_fsubs.
  rewrite multi_subs_subs; try assumption.
  + destruct (in_dec vatomEq.eq_dec x (ffreevars (h2n_formula A))) as [Hf|Hf].
    * eapply exsi; [ | apply ax_hd ].
      clear - f Hcl Hsub Hf.
      apply multi_tsubs_is_closed; [ assumption | ].
      intros a Hin.
      unfold incl in Hsub; specialize Hsub with a; simpl in Hsub.
      assert (In a (hffreevars (hfsubs x t A))) as HvA.
      { rewrite h2n_ffreevars in Hf.
        rewrite h2n_freevars in Hin.
        now apply hffreevars_to_subs. }
      now eapply or_introl in HvA; apply in_or_app in HvA; eapply Hsub in HvA.
    * assert (~ In x (ffreevars (multi_subs (remove_snd x L) (h2n_formula A)))) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_ffreevars in Hin; try assumption.
        clear - Hcl; apply Forall_forall; intros a Hin.
        apply Forall_forall with (x:=a) in Hcl; [ assumption | ].
        revert Hin; clear; induction L; simpl; intros Hin.
        - inversion Hin.
        - destruct a0; simpl; simpl in Hin.
          case_eq (beq_vat x v); intros Heq; rewrite Heq in Hin.
          + now right; apply IHL.
          + inversion Hin as [Hin'|Hin']; simpl in Hin'.
            * now left.
            * now right; apply IHL. }
      rewrite nfree_subs by assumption.
      apply exsi with (dvar 0); [ reflexivity | ].
      rewrite nfree_subs by assumption.
      apply ax_hd.
  + apply Forall_forall; intros z Hinz.
    apply Forall_forall with (x:=z) in f.
    * revert f; clear; hformula_induction A.
      -- apply IHA.
         apply f.
         now rewrite <- h2n_ffreevars.
      -- apply f; [ | assumption ].
         now rewrite <- h2n_ffreevars.
      -- apply IHA.
         apply f.
         now rewrite <- h2n_ffreevars.
      -- apply f; [ | assumption ].
         now rewrite <- h2n_ffreevars.
    * now rewrite <- h2n_freevars.
- rewrite multi_subs_frl.
  rewrite multi_subs_exs.
  rewrite <- multi_subs_remove with (x:=x) in HeqBB; try assumption.
  + apply @exse with (x:=x) (A:=multi_subs (remove_snd x L) (h2n_formula A)); [ apply ax_hd | ].
    apply impe with (subs x (dvar 0) (fupz (multi_subs (remove_snd x L) (h2n_formula A)))); [ | apply ax_hd ].
    replace (imp (subs x (dvar 0) (fupz (multi_subs (remove_snd x L) (h2n_formula A)))) (fupz BB))
       with (subs x (dvar 0) (imp (fupz (multi_subs (remove_snd x L) (h2n_formula A))) (fupz BB))).
    2:{ simpl; f_equal.
        enough (~ In x (ffreevars (fupz BB))) as Hf by now apply nfree_subs.
        intros Hin; apply n; clear - Hcl HeqBB Hin.
        rewrite ffreevars_fup in Hin; subst.
        apply multi_subs_ffreevars in Hin.
        - now rewrite <- h2n_ffreevars.
        - revert Hcl; clear; induction L; simpl; intros Hcl; [ constructor | ].
          destruct a; simpl; simpl in Hcl; inversion Hcl; subst.
          case_eq (beq_vat x v); intros Heq; simpl.
          + now apply IHL.
          + constructor; auto. }
    apply frle; [ reflexivity | ]; simpl.
    change (subs x (dvar 0) (fupz (multi_subs (remove_snd x L) (h2n_formula A)))
             :: exs x (fupz (multi_subs (remove_snd x L) (h2n_formula A)))
             :: frl x (fupz (multi_subs (remove_snd x L) (imp (h2n_formula A) (h2n_formula B)))) :: nil)
      with ((subs x (dvar 0) (fupz (multi_subs (remove_snd x L) (h2n_formula A)))
             :: exs x (fupz (multi_subs (remove_snd x L) (h2n_formula A))) :: nil)
             ++ frl x (fupz (multi_subs (remove_snd x L) (imp (h2n_formula A) (h2n_formula B)))) :: nil).
    rewrite multi_subs_imp; subst.
    apply ax.
  + intros Hin; apply n; clear - Hin.
    now rewrite h2n_ffreevars in Hin.
Qed.





(* From Natural Deduction to Hilbert *)

Section N2H.

Variable r : nat -> hterm.

Fixpoint ltgood_for lv t :=
match t with
| dvar n => Forall (fun x => ~ In x (hfreevars (r n))) lv
| tvar x => True
| tconstr f l => fold_right (fun x P => and (ltgood_for lv x) P) True l
end.

Lemma ltgood_for_less : forall x lv1 lv2 t, ltgood_for (lv1 ++ x :: lv2) t -> ltgood_for (lv1 ++ lv2) t.
Proof. term_induction t; intros HF.
- apply Forall_app_inv in HF; destruct HF as [HF1 HF2].
  apply Forall_app; now inversion HF2.
- apply Forall_fold_right in IHl.
  revert IHl HF; clear; induction l; simpl; intros Hl HF.
  + constructor.
  + destruct Hl as [Hl1 Hl2]; destruct HF as [HF1 HF2]; auto.
Qed.

Lemma ltgood_for_closed : forall l t, (forall n, hclosed (r n)) -> ltgood_for l t.
Proof.
intros l t Hc.
term_induction t.
- rewrite (Hc n).
  apply Forall_forall; auto.
- now apply Forall_fold_right.
Qed.

Fixpoint lgood_for lv A :=
match A with
| var X l => fold_right (fun x P => and (ltgood_for lv x) P) True l
| imp B C => lgood_for lv B /\ lgood_for lv C
| frl z B => lgood_for (z :: lv) B
| exs z B => lgood_for (z :: lv) B
end.

Lemma lgood_for_less : forall x lv1 lv2 A, lgood_for (lv1 ++ x :: lv2) A -> lgood_for (lv1 ++ lv2) A.
Proof. intros x lv1 lv2 A; revert lv1 lv2; formula_induction A.
- revert H; induction l; simpl; intros Hl.
  + constructor.
  + destruct Hl as [Hl1 Hl2]; split; auto.
    now apply ltgood_for_less with x.
- now rewrite app_comm_cons in H; apply IHA in H.
- now rewrite app_comm_cons in H; apply IHA in H.
Qed.

Lemma lgood_for_closed : forall l A, (forall n, hclosed (r n)) -> lgood_for l A.
Proof.
intros l A Hc; revert l.
formula_induction A.
apply Forall_fold_right.
apply Forall_forall; intros.
now apply ltgood_for_closed.
Qed.

Fixpoint n2h_term t :=
match t with
| dvar n => r n
| tvar x => hvar x
| tconstr f l => hconstr f (map n2h_term l)
end.

Lemma n2h_hfreevars : forall t, incl (freevars t) (hfreevars (n2h_term t)).
Proof. term_induction t; intros z Hin.
- inversion Hin.
- revert IHl Hin; induction l; simpl; intros Hl Hin; auto.
  inversion Hl; subst.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; auto.
Qed.

Fixpoint n2h_formula A :=
match A with
| var X l => hfvar X (map n2h_term l)
| imp B C => himp (n2h_formula B) (n2h_formula C)
| frl y B => hfrl y (n2h_formula B)
| exs y B => hexs y (n2h_formula B)
end.

Lemma n2h_tsubs : forall x u t lv, In x lv -> ltgood_for lv t ->
  n2h_term (tsubs x u t) = htsubs x (n2h_term u) (n2h_term t).
Proof. term_induction t; intros lv Hin Hg.
- apply Forall_forall with (x:=x) in Hg; [ | assumption ].
  symmetry; now apply nfree_htsubs.
- f_equal.
  apply map_ext_in; intros a Hina.
  apply Forall_forall with (x:=a) in IHl; [ | assumption ].
  apply (IHl _ Hin).
  apply Forall_fold_right in Hg.
  now apply Forall_forall with (x:=a) in Hg.
Qed.

Lemma n2h_subs : forall x u A lv, In x lv -> lgood_for lv A ->
  n2h_formula (subs x u A) = hfsubs x (n2h_term u) (n2h_formula A).
Proof. formula_induction A.
- now simpl in H0; apply n2h_tsubs with lv.
- now simpl in H0.
- now apply A1 with lv.
- now apply IHA1 with lv.
- case_eq (beq_vat x0 x); intros Heq; simpl; [ reflexivity | ].
  rewrite <- (app_nil_l _) in H0; apply lgood_for_less in H0.
  now f_equal; apply IHA with lv.
- case_eq (beq_vat x0 x); intros Heq; simpl; [ reflexivity | ].
  rewrite <- (app_nil_l _) in H0; apply lgood_for_less in H0.
  now f_equal; apply IHA with lv.
Qed.

Lemma lgood_hgood_closed : forall u x lv lv' A,
  closed u -> lgood_for lv (subs x u A) -> In x lv' -> lgood_for lv' A ->
  Forall (fun y => hgood_for x y (n2h_formula A)) (hfreevars (n2h_term u)).
Proof.
intros u x lv lv' A; revert lv; formula_induction A.
- now apply Forall_forall.
- apply Forall_and.
  + now apply A1 with lv.
  + now apply IHA1 with lv.
- case_eq (beq_vat x0 x); intros Heq; rewrite_all Heq.
  + apply beq_eq_vat in Heq; subst.
    apply Forall_forall; intros z Hz Hin.
    exfalso.
    now apply in_remove in Hin.
  + assert (Hg := H0).
    apply IHA in H0; auto.
    2:{ now rewrite <- (app_nil_l _) in H2; apply lgood_for_less in H2. }
    apply Forall_forall; intros z Hz Hin.
    apply Forall_forall with (x:=z) in H0; [ | assumption ].
    split; [ assumption | ].
    intros Heq2; subst.
    apply in_remove in Hin; destruct Hin as [Hin _].
    simpl in Hg.
    clear - H Hg Hz Hin H1 H2.
    remember (x0 :: lv) as lv0.
    assert (In x0 lv0) by (now subst; constructor); clear lv Heqlv0.
    rewrite <- (app_nil_l _) in H2; apply lgood_for_less in H2; simpl in H2.
    { revert lv0 lv' Hg H0 Hin H1 H2; formula_induction A.
      - apply Forall_fold_right in Hg.
        apply Forall_fold_right in H2.
        revert Hg Hin H2; induction l; simpl; intros Hg Hin H2; [ assumption | ].
        inversion Hg; inversion H2; subst.
        apply in_app_or in Hin; destruct Hin as [Hin|Hin].
        + revert Hin H5 H9; clear - H Hz H0 H1; term_induction a; simpl; intros Hinlv Hg Hlv' .
          * apply Forall_forall with (x:=x) in Hlv'; auto.
          * destruct Hinlv; subst; [ | assumption ].
            rewrite eqb_refl in Hg.
            revert H Hz Hg; clear - H0; term_induction u; simpl; intros Hc Hin Hg.
            -- now apply Forall_forall with (x:=x0) in Hg.
            -- inversion Hc.
            -- apply Forall_fold_right in Hg.
               revert IHl Hc Hin Hg; induction l; simpl; intros Hl Hc Hin Hg; [ assumption | ].
               apply app_eq_nil in Hc.
               inversion Hl; inversion Hg; inversion Hc; subst.
               apply in_app_or in Hin; destruct Hin as [Hin|Hin].
               ++ now apply H2.
               ++ now apply IHl in H3.
          * apply Forall_fold_right in Hg.
            apply Forall_fold_right in Hlv'.
            revert IHl Hinlv Hg Hlv'; induction l; intros; simpl in Hinlv.
            -- inversion Hinlv.
            -- apply in_app_or in Hinlv; destruct Hinlv as [Hinlv|Hinlv].
               ++ inversion IHl0; inversion Hg; inversion Hlv'; subst.
                  apply H4; auto.
               ++ inversion IHl0; inversion Hg; inversion Hlv'; subst.
                  apply IHl; auto.
        + now apply IHl.
      - apply in_app_or in Hin; destruct Hin.
        + now apply A1 with lv0 lv'.
        + now apply IHA1 with lv0 lv'.
      - case_eq (beq_vat x1 x); intros Heq.
        { apply beq_eq_vat in Heq; subst.
          apply in_remove in Hin.
          now apply Hin. }
        rewrite Heq in Hg.
        apply IHA with (x1 :: lv0) (x1 :: lv'); auto.
        + now apply in_cons.
        + now apply in_remove in Hin.
        + now apply in_cons.
      - case_eq (beq_vat x1 x); intros Heq.
        { apply beq_eq_vat in Heq; subst.
          apply in_remove in Hin.
          now apply Hin. }
        rewrite Heq in Hg.
        apply IHA with (x1 :: lv0) (x1 :: lv'); auto.
        + now apply in_cons.
        + now apply in_remove in Hin.
        + now apply in_cons. }
- case_eq (beq_vat x0 x); intros Heq; rewrite_all Heq.
  + apply beq_eq_vat in Heq; subst.
    apply Forall_forall; intros z Hz Hin.
    exfalso.
    now apply in_remove in Hin.
  + assert (Hg := H0).
    apply IHA in H0; auto.
    2:{ now rewrite <- (app_nil_l _) in H2; apply lgood_for_less in H2. }
    apply Forall_forall; intros z Hz Hin.
    apply Forall_forall with (x:=z) in H0; [ | assumption ].
    split; [ assumption | ].
    intros Heq2; subst.
    apply in_remove in Hin; destruct Hin as [Hin _].
    simpl in Hg.
    clear - H Hg Hz Hin H1 H2.
    remember (x0 :: lv) as lv0.
    assert (In x0 lv0) by (now subst; constructor); clear lv Heqlv0.
    rewrite <- (app_nil_l _) in H2; apply lgood_for_less in H2; simpl in H2.
    { revert lv0 lv' Hg H0 Hin H1 H2; formula_induction A.
      - apply Forall_fold_right in Hg.
        apply Forall_fold_right in H2.
        revert Hg Hin H2; induction l; simpl; intros Hg Hin H2; [ assumption | ].
        inversion Hg; inversion H2; subst.
        apply in_app_or in Hin; destruct Hin as [Hin|Hin].
        + revert Hin H5 H9; clear - H Hz H0 H1; term_induction a; simpl; intros Hinlv Hg Hlv' .
          * apply Forall_forall with (x:=x) in Hlv'; auto.
          * destruct Hinlv; subst; [ | assumption ].
            rewrite eqb_refl in Hg.
            revert H Hz Hg; clear - H0; term_induction u; simpl; intros Hc Hin Hg.
            -- now apply Forall_forall with (x:=x0) in Hg.
            -- inversion Hc.
            -- apply Forall_fold_right in Hg.
               revert IHl Hc Hin Hg; induction l; simpl; intros Hl Hc Hin Hg; [ assumption | ].
               apply app_eq_nil in Hc.
               inversion Hl; inversion Hg; inversion Hc; subst.
               apply in_app_or in Hin; destruct Hin as [Hin|Hin].
               ++ now apply H2.
               ++ now apply IHl in H3.
          * apply Forall_fold_right in Hg.
            apply Forall_fold_right in Hlv'.
            revert IHl Hinlv Hg Hlv'; induction l; intros; simpl in Hinlv.
            -- inversion Hinlv.
            -- apply in_app_or in Hinlv; destruct Hinlv as [Hinlv|Hinlv].
               ++ inversion IHl0; inversion Hg; inversion Hlv'; subst.
                  apply H4; auto.
               ++ inversion IHl0; inversion Hg; inversion Hlv'; subst.
                  apply IHl; auto.
        + now apply IHl.
      - apply in_app_or in Hin; destruct Hin.
        + now apply A1 with lv0 lv'.
        + now apply IHA1 with lv0 lv'.
      - case_eq (beq_vat x1 x); intros Heq.
        { apply beq_eq_vat in Heq; subst.
          apply in_remove in Hin.
          now apply Hin. }
        rewrite Heq in Hg.
        apply IHA with (x1 :: lv0) (x1 :: lv'); auto.
        + now apply in_cons.
        + now apply in_remove in Hin.
        + now apply in_cons.
      - case_eq (beq_vat x1 x); intros Heq.
        { apply beq_eq_vat in Heq; subst.
          apply in_remove in Hin.
          now apply Hin. }
        rewrite Heq in Hg.
        apply IHA with (x1 :: lv0) (x1 :: lv'); auto.
        + now apply in_cons.
        + now apply in_remove in Hin.
        + now apply in_cons. }
Qed.



Fixpoint s2f l A :=
match l with
| nil => A
| B :: tl => s2f tl (imp B A)
end.

Notation n2h_sequent l A := (n2h_formula (s2f l A)).

Lemma hprove_Bsequent :
  forall l A B, hprove ((n2h_formula A ⟶ n2h_formula B) ⟶ n2h_sequent l A ⟶ n2h_sequent l B).
Proof.
induction l; intros A B; simpl.
- apply hprove_I.
- specialize IHl with (imp a A) (imp a B); simpl in IHl.
  eapply hprove_CUT; [ | apply IHl ].
  apply hprove_B.
Qed.

Lemma hprove_Ssequent : forall l A B, hprove (n2h_sequent l (imp A B) ⟶ n2h_sequent l A ⟶ n2h_sequent l B).
Proof.
induction l; intros A B; simpl.
- apply hprove_I.
- specialize IHl with (imp a A) (imp a B); simpl in IHl.
  eapply hprove_CUT; [ | apply IHl ].
  eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_S ].
Qed.

Lemma hprove_sequent_imp : forall l A B,
  hprove (n2h_sequent l (imp A B)) -> hprove (n2h_formula A ⟶ n2h_sequent l B).
Proof.
induction l; simpl; intros A B pi; auto.
apply IHl.
eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply pi ]; simpl.
apply hprove_C.
Qed.

Lemma hprove_imp_sequent : forall l A B,
  hprove (n2h_formula A ⟶ n2h_sequent l B) -> hprove (n2h_sequent l (imp A B)).
Proof.
induction l; simpl; intros A B pi; auto.
apply IHl in pi.
eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply pi ]; simpl.
apply hprove_C.
Qed.

Lemma hprove_FRLsequent : forall x l A, ~ In x (flat_map (fun C => hffreevars (n2h_formula C)) l) ->
  hprove ((hfrl x (n2h_sequent l A)) ⟶ n2h_sequent l (frl x A)).
Proof.
induction l; simpl; intros A Hf.
- apply hprove_I.
- eapply hprove_CUT; [ apply IHl | ].
  + intros Hin; apply Hf.
    now apply in_or_app; right.
  + eapply hprove_MP; [ apply hprove_Bsequent | ].
    simpl; apply hprove_FRL.
    intros Hin; apply Hf.
    now apply in_or_app; left.
Qed.

End N2H.



(*
Proposition prove_with_prop_has_prop : forall (P : formula -> Prop),
 (forall A, P (fupz A) -> P A) ->
   (forall l A (pi : nprove l A), nprove_with_prop P pi -> Forall P (A :: l))
 * (forall l A (pi : rprove l A), rprove_with_prop P pi -> Forall P (A :: l)).
Proof.
intros P Hfup.
apply rnprove_mutrect ; intros.
- inversion H.
  destruct H1.
  constructor; auto.
  apply Forall_app; auto.
- inversion H1.
  destruct H3.
  apply H in H3.
  inversion H3; subst.
  auto.
- inversion H0.
  apply H in H2.
  inversion H2.
  auto.
- now apply H in H0.
- inversion H0.
  apply H in H2.
  inversion H2; inversion H6; auto.
- inversion H0.
  apply H in H2.
  inversion H2.
  constructor; auto.
  clear - Hfup H6.
  revert H6; induction l; simpl; intros Hf; constructor; inversion Hf; subst; auto.
- inversion H0.
  apply H in H2.
  inversion H2; auto.
- inversion H1.
  destruct H3.
  apply H in H3.
  inversion H3; auto.
Qed.
*)

(*
Theorem subformula_prop_hered : forall (P : formula -> Prop), (forall A B, subform A B -> P B -> P A) ->
   (forall l A (pi : nprove l A), Forall P (A :: l) -> nprove_with_prop P pi)
 * (forall l A (pi : rprove l A), Forall P (A :: l) -> rprove_with_prop P pi).
Proof.
intros P HP; split; intros l A pi HF.
- assert (Hn := fst subformula_prop _ _ pi).
  destruct Hn as [_ Hn].
  apply rnprove_stronger with (Q := P) in Hn; [ assumption | ].
  intros x Hs.
  remember (A :: l) as s.
  revert Hs HF; clear - HP; induction s; intros Hs HF; inversion Hs; inversion HF; subst; auto.
  apply HP with a; auto.
- assert (Hr := snd subformula_prop _ _ pi).
  apply rnprove_stronger with (Q := P) in Hr; [ assumption | ].
  intros x Hs.
  remember (A :: l) as s.
  revert Hs HF; clear - HP; induction s; intros Hs HF; inversion Hs; inversion HF; subst; auto.
  apply HP with a; auto.
Qed.
*)



(*
Inductive lsubform : formula -> formula -> Prop :=
| lsub_id : forall A, lsubform A A
| lsub_imp_r : forall A B C, lsubform (imp A B) C -> lsubform B C
| lsub_frl : forall A x u B, lsubform (frl x A) B -> lsubform (subs x u A) B
| lsub_ex : forall A x u B, lsubform (exs x A) B -> lsubform (subs x u A) B.

Lemma lsubform_trans : forall A B C, lsubform A B -> lsubform B C -> lsubform A C.
Proof.
intros A B C Hl Hr ; revert C Hr ; induction Hl ; intros C' Hr; auto;
  try (econstructor; now apply IHHl).
Qed.

Lemma subform_fupz : forall A B, subform A B -> subform (fupz A) (fupz B).
Proof.
intros A B Hs; induction Hs; try (now econstructor; eauto).
- rewrite fup_subs_com in IHHs.
  now econstructor; eauto.
- rewrite fup_subs_com in IHHs.
  now econstructor; eauto.
- eapply subform_trans; [ apply IHHs | ].
  simpl; rewrite fup_subs_com.
  econstructor.
  econstructor.
  rewrite fup_subs_com.
  apply sub_id.
- eapply subform_trans; [ apply IHHs | ].
  simpl; rewrite fup_subs_com.
  econstructor.
  econstructor.
  rewrite fup_subs_com.
  apply sub_id.
Qed.

Lemma lsubform_subform : forall A B, lsubform A B -> subform A B.
Proof.
intros A B Hs; induction Hs.
- apply sub_id.
- apply subform_trans with (imp A B); auto.
  now constructor; constructor.
- apply subform_trans with (frl x A); auto.
  now econstructor; constructor.
- apply subform_trans with (exs x A); auto.
  now econstructor; constructor.
Qed.

Theorem lsubformula_prop :
   (forall l A (pi : nprove l A), Exists (lsubform A) l
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
    apply lsubform_trans with (imp A' B'); auto.
    econstructor; constructor.
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      apply lsubform_subform in HsD.
      eapply subform_trans; eassumption.
    * constructor ; assumption.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      eapply subform_trans ; [ eassumption | ].
      apply lsubform_subform in HsD.
      apply subform_trans  with (imp A' B'); [ constructor ; constructor | eassumption ].
    * constructor ; assumption.
- intros x l' A' u Hc pi [Hn Hs] ; repeat split.
  + eapply Exists_impl ; [ | eassumption ].
    intros C HsC.
    eapply lsubform_trans ; [ econstructor ; constructor | eassumption ].
  + constructor ; constructor.
  + eapply rnprove_stronger ; [ | eassumption ] ; simpl.
    intros C HsC.
    inversion HsC ; subst.
    * apply Exists_cons_tl.
      eapply Exists_impl ; [ | eassumption ].
      intros D HsD.
      apply lsubform_subform in HsD.
      eapply subform_trans; eassumption.
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
      apply lsubform_subform in HsE.
      eapply subform_trans; eassumption.
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
         apply lsubform_subform in HsE.
         eapply subform_trans with (exs x A'); [ constructor ; constructor | eassumption ].
      -- revert H1 ; clear ; induction l' ; intros H ; inversion H ; subst.
         ++ constructor.
            eapply subform_trans ; [ eassumption | constructor ; constructor ].
         ++ apply Exists_cons_tl ; intuition.
Qed.
*)
















Notation n2h_sequent r l A := (n2h_formula r (s2f l A)).
Notation rgood_for r := (lgood_for r nil).

Fixpoint allvars A :=
match A with
| var _ l => concat (map freevars l)
| imp B C => allvars B ++ allvars C
| frl x B => x :: allvars B
| exs x B => x :: allvars B
end.

Lemma ffreevars_allvars : forall A, incl (ffreevars A) (allvars A).
Proof.
formula_induction A.
- intros z Hz.
  apply in_cons.
  apply in_remove in Hz; destruct Hz.
  now apply IHA.
- intros z Hz.
  apply in_cons.
  apply in_remove in Hz; destruct Hz.
  now apply IHA.
Qed.

Fixpoint hallvars A :=
match A with
| hfvar _ l => concat (map hfreevars l)
| himp B C => hallvars B ++ hallvars C
| hfrl x B => x :: hallvars B
| hexs x B => x :: hallvars B
end.

Lemma hffreevars_hallvars : forall A, incl (hffreevars A) (hallvars A).
Proof.
hformula_induction A.
- intros z Hz.
  apply in_cons.
  apply in_remove in Hz; destruct Hz.
  now apply IHA.
- intros z Hz.
  apply in_cons.
  apply in_remove in Hz; destruct Hz.
  now apply IHA.
Qed.

Lemma htbisubs : forall x y t, ~ In x (hfreevars t) ->
  htsubs x (hvar y) (htsubs y (hvar x) t) = t.
Proof. hterm_induction t; intros Hin.
- case_eq (beq_vat x0 y); simpl; intros Heq.
  + rewrite eqb_refl.
    now apply beq_eq_vat in Heq; subst.
  + case_eq (beq_vat x0 x); intros Heq2; auto.
    exfalso; apply Hin.
    now apply beq_eq_vat in Heq2; left.
- f_equal.
  rewrite <- (map_id l) at 2.
  apply map_ext_in; intros z Hz.
  apply Forall_forall with (x:=z) in IHl; auto.
  apply IHl.
  intros Hin2; apply Hin.
  revert Hz; clear - Hin2; induction l; intros Hin; inversion Hin; subst.
  + now simpl; apply in_or_app; left.
  + apply IHl in H.
    now simpl; apply in_or_app; right.
Qed.

Lemma hbisubs : forall x y A, ~ In x (hallvars A) ->
  hfsubs x (hvar y) (hfsubs y (hvar x) A) = A.
Proof. hformula_induction A.
- apply htbisubs.
  intros Hin; apply H.
  now simpl; apply in_or_app; left.
- apply H.
  now simpl; apply in_or_app; right.
- case_eq (beq_vat x0 y); simpl; intros Heq; case_eq (beq_vat x0 x); intros Heq2; auto; f_equal; auto.
  + apply nfree_hfsubs.
    intros Hin; apply H1.
    now apply hffreevars_hallvars.
  + apply beq_eq_vat in Heq2; subst.
    now exfalso.
- case_eq (beq_vat x0 y); simpl; intros Heq; case_eq (beq_vat x0 x); intros Heq2; auto; f_equal; auto.
  + apply nfree_hfsubs.
    intros Hin; apply H1.
    now apply hffreevars_hallvars.
  + apply beq_eq_vat in Heq2; subst.
    now exfalso.
Qed.

Lemma n2h_allvars : forall r A,
  incl (allvars A ++ hffreevars (n2h_formula r A)) (hallvars (n2h_formula r A)).
Proof. formula_induction A; simpl; intros z Hin.
- revert Hin; induction l; simpl; intros Hin.
  + assumption.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
    apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; auto.
    * now apply n2h_hfreevars.
    * apply IHl.
      apply in_or_app; auto.
- apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right].
    * apply A1.
      now apply in_or_app; left.
    * apply IHA1.
      now apply in_or_app; left.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right].
    * apply A1.
      now apply in_or_app; right.
    * apply IHA1.
      now apply in_or_app; right.
- inversion Hin; subst.
  + now constructor.
  + apply in_cons, IHA.
    apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right]; auto.
    now apply in_remove in H.
- inversion Hin; subst.
  + now constructor.
  + apply in_cons, IHA.
    apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right]; auto.
    now apply in_remove in H.
Qed.

Definition rsubs x y (r : nat -> hterm) n := htsubs x (hvar y) (r n).

Lemma tgood_for_fresh : forall r y x t, ~ In y (freevars t) -> forall lv, ~ In y lv ->
  ltgood_for r lv t -> ltgood_for (rsubs x y r) lv t.
Proof.
term_induction t; intros Hin lv Hin2 Hg.
- revert Hin2 Hg; clear; induction lv; simpl; intros Hin Hg; constructor; inversion Hg; subst; auto.
  intros Hin2; apply H1.
  unfold rsubs in Hin2.
  apply hfreevars_tsubs in Hin2; destruct Hin2 as [Hin2|Hin2]; simpl in Hin2.
  + exfalso; destruct Hin2; destruct H; auto.
  + now destruct Hin2.
- apply Forall_fold_right; apply Forall_fold_right in Hg.
  revert IHl Hin Hg; induction l; simpl; intros Hl Hin Hg; constructor; inversion Hg; inversion Hl; subst; auto.
  + apply H5; auto.
    intros Hin3; apply Hin.
    apply in_or_app; auto.
  + apply IHl; auto.
    intros Hin3; apply Hin.
    apply in_or_app; auto.
Qed.

Lemma good_for_fresh : forall r y x A, ~ In y (allvars A) -> forall lv, ~ In y lv ->
  lgood_for r lv A -> lgood_for (rsubs x y r) lv A.
Proof.
formula_induction A.
- apply Forall_fold_right in H1; apply Forall_fold_right.
  revert H H1; induction l; simpl; intros Hin HF; constructor; inversion HF; subst.
  + apply tgood_for_fresh; auto.
    intros Hin2; apply Hin.
    apply in_or_app; auto.
  + apply IHl; auto.
    intros Hin2; apply Hin.
    apply in_or_app; auto.
- apply H; auto.
  intros Hin; inversion Hin; auto.
- apply H; auto.
  intros Hin; inversion Hin; auto.
Qed.




Parameter vfresh : list vatom -> vatom.
Parameter vfresh_prop : forall l, ~ In (vfresh l) l .

Require Import Lia.

Definition nat_fresh l := S (fold_right max 0 l).
Lemma nat_fresh_prop : forall l, ~ In (nat_fresh l) l.
Proof.
enough (forall l n h, ~ In (n + nat_fresh (h ++ l)) l) as Hh
 by (intros l; rewrite <- (app_nil_l l) at 1; apply (Hh _ 0)).
induction l; unfold nat_fresh; simpl; intros n h Hin; auto.
destruct Hin as [Hin|Hin].
- enough (a < n + S (fold_right Init.Nat.max 0 (h ++ a :: l))) by lia.
  clear; induction h; simpl; lia.
- apply IHl with n (h ++ a :: nil).
  now rewrite <- app_assoc.
Qed.







Fixpoint rrefresh l ld r :=
match l with
| nil => r
| x :: tl => let y := vfresh (l ++ ld) in rrefresh tl (x :: y :: ld) (rsubs x y r)
end.

Lemma hfreevars_rrefresh : forall n l ld r z,
  In z ld -> In z (hfreevars (rrefresh l ld r n)) -> In z (hfreevars (r n)).
Proof.
induction l; intros ld r z Hinz Hin; simpl in Hin; auto.
apply IHl in Hin.
- unfold rsubs in Hin.
  apply hfreevars_tsubs in Hin.
  destruct Hin as [Hin|Hin].
  + exfalso.
    simpl in Hin; destruct Hin as [Hin _].
    destruct Hin; auto.
    apply vfresh_prop with (a :: l ++ ld).
    rewrite H.
    apply in_cons.
    now apply in_or_app; right.
  + now destruct Hin.
- now apply in_cons, in_cons.
Qed.

Lemma rrefresh_notin : forall n z lvA lv r,
  In z lvA -> In z (hfreevars (rrefresh lvA lv r n)) -> False.
Proof.
induction lvA; intros lv r Hinz Hin; inversion Hinz; subst; simpl in Hin.
- clear - Hin.
  apply hfreevars_rrefresh in Hin.
  + unfold rsubs in Hin.
    apply hfreevars_tsubs in Hin.
    destruct Hin as [Hin|Hin].
    * destruct Hin as [Hin _].
      simpl in Hin; destruct Hin; auto.
      apply vfresh_prop with (z :: lvA ++ lv).
      rewrite H.
      now constructor.
    * now destruct Hin.
  + now constructor.
- apply IHlvA in Hin; auto.
Qed.

Lemma good_for_refresh_preserv : forall l r ld lv A, incl (allvars A) ld -> incl lv ld ->
  lgood_for r lv A -> lgood_for (rrefresh l ld r) lv A.
Proof.
induction l; intros r ld lv A HA Hlv Hg; simpl; auto.
apply IHl.
- intros z Hz.
  apply in_cons, in_cons.
  apply HA, Hz.
- intros z Hz.
  apply in_cons, in_cons.
  apply Hlv, Hz.
- apply good_for_fresh; auto; intros Hin.
  + apply HA in Hin.
    apply vfresh_prop with (a :: l ++ ld).
    apply in_cons.
    now apply in_or_app; right.
  + apply Hlv in Hin.
    apply vfresh_prop with (a :: l ++ ld).
    apply in_cons.
    now apply in_or_app; right.
Qed.

Lemma good_for_refresh : forall ld A r lvA lv, incl (hallvars (n2h_formula r A) ++ lv) lvA ->
  lgood_for (rrefresh lvA ld r) lv A.
Proof. formula_induction A.
- apply Forall_fold_right.
  revert H; induction l; intros HlvA; constructor.
  + clear IHl; term_induction a; simpl.
    * apply Forall_forall; intros z Hz Hin.
      eapply rrefresh_notin; [ | eassumption ].
      apply HlvA; now apply in_or_app; right.
    * apply Forall_fold_right.
      apply Forall_forall; intros t Ht.
      apply Forall_forall with (x:=t) in IHl; auto.
  + clear - HlvA.
    apply Forall_forall; intros t Ht.
    term_induction t; auto.
    * apply Forall_forall; intros z Hz Hin.
      eapply rrefresh_notin; [ | eassumption ].
      apply HlvA; now apply in_or_app; right.
    * apply Forall_fold_right.
      apply Forall_forall; intros u Hu.
      apply Forall_forall with (x:=u) in IHl; auto.
- apply A1.
  intros z Hz; apply H.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; auto.
  now apply in_or_app; left.
- apply IHA1.
  intros z Hz; apply H.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; auto.
  now apply in_or_app; right.
- apply IHA.
  intros z Hz.
  apply H.
  apply in_app_or in Hz; destruct Hz as [Hz|Hz]; auto.
  + right; now apply in_or_app; left.
  + destruct Hz; [left|right]; auto.
    now apply in_or_app; right.
- apply IHA.
  intros z Hz.
  apply H.
  apply in_app_or in Hz; destruct Hz as [Hz|Hz]; auto.
  + right; now apply in_or_app; left.
  + destruct Hz; [left|right]; auto.
    now apply in_or_app; right.
Qed.

Lemma bisubs_fresh : forall r y x A,
  ~ In y (allvars A) -> ~ In y (hffreevars (n2h_formula r A)) ->
  hfsubs y (hvar x) (n2h_formula (rsubs x y r) A) = n2h_formula r A.
Proof.
formula_induction A.
- revert H H0; clear; term_induction t; simpl; intros Hin Hinf.
  + unfold rsubs.
    remember (r n) as u; revert Hinf; clear; hterm_induction u; simpl; intros Hinf.
    * case_eq (beq_vat x0 x); intros Heq; simpl.
      -- rewrite eqb_refl.
         now apply beq_eq_vat in Heq; subst.
      -- case_eq (beq_vat x0 y); intros Heq2; simpl.
         ++ exfalso; apply Hinf; left.
            now apply beq_eq_vat in Heq2.
         ++ reflexivity.
    * f_equal.
      rewrite <- (map_id l) at 2.
      apply map_ext_in; intros a Hina.
      apply Forall_forall with (x:=a) in IHl; auto.
      apply IHl.
      intros Hin; apply Hinf.
      apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [ left | right ]; subst; auto.
      -- revert Hina; clear - Hin; induction l; simpl; intros Hin2; auto.
         apply in_or_app; destruct Hin2 as [Hin2|Hin2]; [ left | right ]; subst; auto.
      -- now rewrite map_map in Hin.
  + case_eq (beq_vat x0 y); intros Heq; auto.
    apply beq_eq_vat in Heq.
    exfalso; apply Hin; auto.
  + f_equal.
    apply map_ext_in; intros a Hina.
    apply Forall_forall with (x:=a) in IHl; [ | assumption ].
    apply IHl.
    * simpl; intros Hin2; apply Hin.
      apply in_or_app; apply in_app_or in Hin2; destruct Hin2 as [Hin2|Hin2]; [ left | right ]; auto.
      revert Hina; clear - Hin2; induction l; simpl; intros Hin; auto.
      apply in_or_app; destruct Hin as [Hin|Hin]; [ left | right ]; subst; auto.
    * simpl; intros Hin2.
      apply Hinf.
      apply in_or_app; apply in_app_or in Hin2; destruct Hin2 as [Hin2|Hin2]; [left|right].
      -- revert Hina; clear - Hin2; induction l; simpl; intros Hin; auto.
         apply in_or_app; destruct Hin as [Hin|Hin]; [ left | right ]; subst; auto.
      -- now rewrite map_map in Hin2.
- apply H.
  simpl; apply in_or_app; auto.
- apply H0.
  simpl; apply in_or_app; right; auto.
- case_eq (beq_vat x0 y); intros Heq; f_equal; auto.
  + exfalso; apply beq_eq_vat in Heq; auto.
  + apply H.
    intros Hin; apply H0.
    apply notin_remove; auto.
- case_eq (beq_vat x0 y); intros Heq; f_equal; auto.
  + exfalso; apply beq_eq_vat in Heq; auto.
  + apply H.
    intros Hin; apply H0.
    apply notin_remove; auto.
Qed.

Lemma good_for_hilbert_rsubs : forall r y x A,
  ~ In y (allvars A) -> ~ In y (hffreevars (n2h_formula r A)) -> rgood_for r A ->
  hprove (n2h_formula (rsubs x y r) A) -> hprove (n2h_formula r A).
Proof.
intros r y x A Hin Hinf Hg pi.
rewrite <- bisubs_fresh with (x:=x) (y:=y); auto.
eapply hprove_MP; [ apply hprove_INST | apply hprove_GEN ]; auto.
simpl; repeat constructor.
revert Hin Hinf Hg; clear.
induction A; simpl; intros; auto.
- split.
  + apply IHA1.
    * intros Hin2; apply Hin.
      apply in_or_app; auto.
    * intros Hin2; apply Hinf.
      apply in_or_app; auto.
    * destruct Hg; auto.
  + apply IHA2.
    * intros Hin2; apply Hin.
      apply in_or_app; auto.
    * intros Hin2; apply Hinf.
      apply in_or_app; auto.
    * destruct Hg; auto.
- split.
  + apply IHA; auto.
    * rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
      intros Heq; subst.
      apply in_remove in H; destruct H.
      apply Hinf.
      apply notin_remove; auto.
    * rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
  + intros Heq; subst.
    revert Hinf H Hin Hg; clear; formula_induction A.
    * apply Forall_fold_right in Hg.
      apply in_remove in H; destruct H.
      apply Hinf.
      apply notin_remove; auto.
      revert H Hin Hg; clear; induction l; simpl; intros; auto.
      inversion Hg; subst.
      apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right].
      -- revert H H2 Hin; clear; term_induction a; intros.
         ++ unfold rsubs in H.
            inversion H2; subst.
            apply hfreevars_tsubs in H; destruct H; auto.
            ** exfalso; destruct H; auto.
            ** now destruct H.
         ++ apply Forall_fold_right in H2.
            revert IHl H H2 Hin; induction l0; intros Hl Hin Hg Hnin.
            ** inversion Hin.
            ** simpl; apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right];
               inversion Hl; inversion Hg; subst.
               --- apply H1; auto.
                   intros Hnin2; apply Hnin.
                   destruct Hnin2; auto.
                   right.
                   apply in_or_app; apply in_app_or in H; destruct H; [left|right]; auto.
                   apply in_or_app; left; auto.
               --- apply IHl0; auto.
                   intros Hnin2; apply Hnin.
                   destruct Hnin2; auto.
                   right.
                   simpl; rewrite <- app_assoc.
                   apply in_or_app; right; auto.
      -- apply IHl; auto.
         intros Hin2; apply Hin.
         destruct Hin2; auto.
         right.
         apply in_or_app; auto.
    * apply in_remove in H; destruct H.
      apply in_app_or in H; destruct H as [H|H].
      -- apply A1; auto; intros.
         ++ apply Hinf.
            apply notin_remove; auto.
            apply in_or_app; left.
            apply in_remove in H5; destruct H5; auto.
         ++ apply notin_remove; auto.
         ++ destruct H5; auto.
            apply H3.
            apply in_or_app; auto.
      -- apply IHA1; auto; intros.
         ++ apply Hinf.
            apply notin_remove; auto.
            apply in_or_app; right.
            apply in_remove in H5; destruct H5; auto.
         ++ apply notin_remove; auto.
         ++ destruct H5; auto.
            apply H3.
            apply in_or_app; auto.
    * apply IHA; auto; intros.
      apply Hinf.
      apply notin_remove; auto.
      apply notin_remove; auto.
      apply in_remove in H1; destruct H1; auto.
      apply notin_remove; auto.
      apply in_remove in H; destruct H.
      apply in_remove in H; destruct H; auto.
      destruct H1; auto.
      rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
    * apply IHA; auto; intros.
      apply Hinf.
      apply notin_remove; auto.
      apply notin_remove; auto.
      apply in_remove in H1; destruct H1; auto.
      apply notin_remove; auto.
      apply in_remove in H; destruct H.
      apply in_remove in H; destruct H; auto.
      destruct H1; auto.
      rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
- split.
  + apply IHA; auto.
    * rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
      intros Heq; subst.
      apply in_remove in H; destruct H.
      apply Hinf.
      apply notin_remove; auto.
    * rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
  + intros Heq; subst.
    revert Hinf H Hin Hg; clear; formula_induction A.
    * apply Forall_fold_right in Hg.
      apply in_remove in H; destruct H.
      apply Hinf.
      apply notin_remove; auto.
      revert H Hin Hg; clear; induction l; simpl; intros; auto.
      inversion Hg; subst.
      apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right].
      -- revert H H2 Hin; clear; term_induction a; intros.
         ++ unfold rsubs in H.
            inversion H2; subst.
            apply hfreevars_tsubs in H; destruct H; auto.
            ** exfalso; destruct H; auto.
            ** now destruct H.
         ++ apply Forall_fold_right in H2.
            revert IHl H H2 Hin; induction l0; intros Hl Hin Hg Hnin.
            ** inversion Hin.
            ** simpl; apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right];
               inversion Hl; inversion Hg; subst.
               --- apply H1; auto.
                   intros Hnin2; apply Hnin.
                   destruct Hnin2; auto.
                   right.
                   apply in_or_app; apply in_app_or in H; destruct H; [left|right]; auto.
                   apply in_or_app; left; auto.
               --- apply IHl0; auto.
                   intros Hnin2; apply Hnin.
                   destruct Hnin2; auto.
                   right.
                   simpl; rewrite <- app_assoc.
                   apply in_or_app; right; auto.
      -- apply IHl; auto.
         intros Hin2; apply Hin.
         destruct Hin2; auto.
         right.
         apply in_or_app; auto.
    * apply in_remove in H; destruct H.
      apply in_app_or in H; destruct H as [H|H].
      -- apply A1; auto; intros.
         ++ apply Hinf.
            apply notin_remove; auto.
            apply in_or_app; left.
            apply in_remove in H5; destruct H5; auto.
         ++ apply notin_remove; auto.
         ++ destruct H5; auto.
            apply H3.
            apply in_or_app; auto.
      -- apply IHA1; auto; intros.
         ++ apply Hinf.
            apply notin_remove; auto.
            apply in_or_app; right.
            apply in_remove in H5; destruct H5; auto.
         ++ apply notin_remove; auto.
         ++ destruct H5; auto.
            apply H3.
            apply in_or_app; auto.
    * apply IHA; auto; intros.
      apply Hinf.
      apply notin_remove; auto.
      apply notin_remove; auto.
      apply in_remove in H1; destruct H1; auto.
      apply notin_remove; auto.
      apply in_remove in H; destruct H.
      apply in_remove in H; destruct H; auto.
      destruct H1; auto.
      rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
    * apply IHA; auto; intros.
      apply Hinf.
      apply notin_remove; auto.
      apply notin_remove; auto.
      apply in_remove in H1; destruct H1; auto.
      apply notin_remove; auto.
      apply in_remove in H; destruct H.
      apply in_remove in H; destruct H; auto.
      destruct H1; auto.
      rewrite <- (app_nil_l _) in Hg; apply lgood_for_less in Hg; auto.
Qed.

Lemma good_for_hilbert_rrefresh : forall l r ld A,
  incl (hallvars (n2h_formula r A)) ld -> rgood_for r A ->
  hprove (n2h_formula (rrefresh l ld r) A) -> hprove (n2h_formula r A).
Proof.
induction l; intros r ld A HA Hg pi; simpl; auto.
apply IHl in pi.
- apply good_for_hilbert_rsubs in pi; auto.
  + intros Hin.
    apply vfresh_prop with (a :: l ++ ld).
    apply in_cons.
    apply in_or_app; right.
    apply HA.
    apply n2h_allvars.
    now apply in_or_app; left.
  + intros Hin.
    apply vfresh_prop with (a :: l ++ ld).
    apply in_cons.
    apply in_or_app; right.
    apply HA.
    apply n2h_allvars.
    now apply in_or_app; right.
- intros z Hz.
  unfold rsubs in Hz.
  revert HA Hz; clear; formula_induction A; subst.
  + revert HA Hz; induction l0; simpl; intros HA Hz; auto.
    apply in_app_or in Hz; destruct Hz as [Hz|Hz].
    * right.
      revert HA Hz; clear; term_induction a0; simpl; intros HA Hz.
      -- apply hfreevars_tsubs in Hz; destruct Hz as [Hz|Hz]; destruct Hz.
         ++ left.
            simpl in H; now destruct H.
         ++ right.
            apply HA.
            now apply in_or_app; left.
      -- destruct Hz; subst; try now idtac.
         right.
            apply HA.
          now constructor.
      -- revert IHl HA Hz; induction l1; simpl; intros Hl HA Hz; [inversion Hz |].
         inversion Hl; subst.
         apply in_app_or in Hz; destruct Hz as [Hz | Hz].
         ++ apply H1 in Hz; auto.
            intros y Hy; apply HA.
            rewrite map_map in Hy.
            apply in_or_app; apply in_app_or in Hy; destruct Hy as [Hy|Hy]; [left|right]; auto.
            now apply in_or_app; left.
         ++ apply IHl1 in Hz; auto.
            intros y Hy; apply HA.
            apply in_or_app; apply in_app_or in Hy; destruct Hy as [Hy|Hy]; [left|right]; auto.
            now apply in_or_app; right.
    * apply IHl0 in Hz; auto.
      intros y Hy; apply HA.
      now apply in_or_app; right.
  + apply in_app_or in Hz; destruct Hz as [Hz|Hz].
    * apply A1; auto.
      intros y Hy; apply HA.
      now apply in_or_app; left.
    * apply IHA1; auto.
      intros y Hy; apply HA.
      now apply in_or_app; right.
  + right; right.
    apply HA; now constructor.
  + apply IHA; auto.
    intros y Hz; apply HA; now constructor.
  + right; right.
    apply HA; now constructor.
  + apply IHA; auto.
    intros y Hz; apply HA; now constructor.
- apply good_for_fresh; auto.
  intros Hin.
  apply vfresh_prop with (a :: l ++ ld).
  apply in_cons.
  apply in_or_app; right.
  apply HA.
  apply n2h_allvars.
  now apply in_or_app; left.
Qed.


Definition rup t r n : hterm :=
match n with
| 0 => t
| S k => r k
end.

Lemma good_for_rup_term : forall t r u lv, ltgood_for r lv u -> ltgood_for (rup t r) lv (tup 0 u).
Proof.
term_induction u; intros lv HF.
apply Forall_fold_right in HF; apply Forall_fold_right.
apply Forall_forall; intros x Hx.
apply in_map_iff in Hx.
destruct Hx as [y [Heq Hy]]; subst.
apply Forall_forall with (x:=y) in HF; [ apply Forall_forall with (x:=y) in IHl | ]; auto.
Qed.

Lemma good_for_rup : forall t r A lv, lgood_for r lv A -> lgood_for (rup t r) lv (fupz A).
Proof.
formula_induction A.
apply Forall_fold_right in H; apply Forall_fold_right.
revert H; induction l; simpl; intros HF; inversion HF; subst; constructor.
- now apply good_for_rup_term.
- now apply IHl.
Qed.

Lemma good_for_rup_tsubs : forall r x y lv t,
  ~ In y lv -> ~ In y (hfreevars (n2h_term r t)) ->
  ltgood_for r lv t ->  ltgood_for (rup (hvar y) r) lv (tsubs x (dvar 0) (tup 0 t)).
Proof.
term_induction t; intros Hlv Hy Hg.
- case_eq (beq_vat x0 x); intros Heq; simpl; auto.
  apply Forall_forall; intros z Hz; intros Heqz.
  apply Hy; destruct Heqz; subst.
  + now exfalso.
  + inversion H.
- apply Forall_fold_right; apply Forall_fold_right in Hg.
  apply Forall_forall; intros z Hz.
  apply in_map_iff in Hz; destruct Hz as [z' [Heq Hz]]; subst.
  apply Forall_forall with (x:=z') in Hg; apply Forall_forall with (x:=z') in IHl; auto.
  apply IHl; auto.
  intros Hin; apply Hy.
  revert Hz Hin; clear; induction l; simpl; intros Hz Hin; inversion Hz; subst.
  + now apply in_or_app; left.
  + apply in_or_app; right.
    now apply IHl.
Qed.

Lemma good_for_rup_subs : forall r x y A lv,
  In x lv -> ~ In y lv -> ~ In y (hallvars (n2h_formula r A)) ->
  lgood_for r lv A ->  lgood_for (rup (hvar y) r) lv (subs x (dvar 0) (fupz A)).
Proof. formula_induction A;
try rename H into Hxlv; try rename H0 into Hylv; try rename H1 into Hyl; try rename H2 into Hg.
- apply Forall_fold_right in Hg; apply Forall_fold_right.
  apply Forall_forall; intros t Ht.
  rewrite map_map in Ht.
  apply in_map_iff in Ht; destruct Ht as [u [Heq Hu]]; subst.
  apply Forall_forall with (x:=u) in Hg; [ | assumption ].
  apply good_for_rup_tsubs; auto.
  intros Hin; apply Hyl.
  revert Hu Hin; clear; induction l; simpl; intros Hu Hin; inversion Hu; subst.
  + now apply in_or_app; left.
  + apply in_or_app; right.
    now apply IHl.
- case_eq (beq_vat x0 x); intros Heq; simpl.
  + now apply good_for_rup.
  + apply IHA; auto.
    * now apply in_cons.
    * intros Hin; apply Hylv.
      destruct Hin as [Hin|Hin]; subst; auto.
      now exfalso.
- case_eq (beq_vat x0 x); intros Heq; simpl.
  + now apply good_for_rup.
  + apply IHA; auto.
    * now apply in_cons.
    * intros Hin; apply Hylv.
      destruct Hin as [Hin|Hin]; subst; auto.
      now exfalso.
Qed.

Lemma n2h_rup_term : forall t u r, n2h_term (rup t r) (tup 0 u) = n2h_term r u.
Proof.
term_induction u; intros r; f_equal.
rewrite map_map.
apply map_ext_in.
intros a Ha.
apply Forall_forall with (x:=a) in IHl; auto.
Qed.

Lemma n2h_rup : forall t A r, n2h_formula (rup t r) (fupz A) = n2h_formula r A.
Proof. formula_induction A; apply n2h_rup_term. Qed.

Lemma n2h_rup_subs : forall x lv t A r, In x lv -> lgood_for r lv A ->
  n2h_formula (rup t r) (subs x (dvar 0) (fupz A)) = hfsubs x t (n2h_formula r A).
Proof.
intros.
rewrite n2h_subs with (lv:=lv); auto.
- f_equal.
  apply n2h_rup.
- now apply good_for_rup.
Qed.

Proposition n2h :
   (forall l A, nprove l A -> forall r, Forall (rgood_for r) (A :: l) -> hprove (n2h_sequent r l A))
 * (forall l A, rprove l A -> forall r, Forall (rgood_for r) (A :: l) -> hprove (n2h_sequent r l A)).
Proof.
apply rnprove_mutrect ; intros.
- induction l1; simpl.
  + induction l2; simpl.
    * apply hprove_I.
    * eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_K ] | apply IHl2 ].
      simpl in H; inversion H; inversion H3; inversion H7; subst.
      now simpl; repeat constructor.
  + eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | apply hprove_K ] | apply IHl1 ].
    inversion H; inversion H3; subst.
    now constructor.
- assert ({rf : _ & Forall (rgood_for rf) (imp A B :: l)
                  & hprove (n2h_sequent rf l B) -> hprove (n2h_sequent r0 l B)})
    as [rf Hg Hp].
  { exists (rrefresh (hallvars (n2h_formula r0 A))
                     (flat_map (fun C => hallvars (n2h_formula r0 C)) (B :: l)) r0).
    - constructor; simpl; [split | ].
      + apply good_for_refresh.
        rewrite app_nil_r.
        now intros z Hz.
      + apply good_for_refresh_preserv.
        * intros z Hz; apply in_or_app; left.
          apply n2h_allvars; now apply in_or_app; left.
        * intros z Hz; inversion Hz.
        * now inversion H.
      + apply Forall_forall; intros C HC.
        apply good_for_refresh_preserv.
        * intros z Hz; apply in_or_app; right.
          revert HC; clear - Hz; induction l; intros Hin; inversion Hin; subst; simpl.
          -- apply in_or_app; left.
             apply n2h_allvars; now apply in_or_app; left.
          -- apply IHl in H.
             now apply in_or_app; right.
        * intros z Hz; inversion Hz.
        * inversion H; subst.
          now apply Forall_forall with (x:=C) in H3.
    - apply good_for_hilbert_rrefresh.
      + intros z Hz; simpl.
        clear - Hz.
        revert B Hz; induction l; simpl; intros B Hz.
        * now apply in_or_app; left.
        * apply IHl in Hz.
          apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz].
          -- simpl in Hz; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [right|left]; auto.
             now apply in_or_app; left.
          -- right; now apply in_or_app; right.
      + clear - H.
        revert B H; induction l; intros B HF; inversion HF; subst; simpl; auto.
        inversion H2; subst.
        apply IHl; constructor; auto.
        now split. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Ssequent | apply X ] | apply X0 ]; auto.
  now inversion Hg; inversion H2; constructor.
- assert ({rf : _ & Forall (rgood_for rf) (frl x A :: l) /\ rgood_for rf (subs x u A)
                  & hprove (n2h_sequent rf l (subs x u A)) -> hprove (n2h_sequent r l (subs x u A))})
    as [rf [Hg1 Hg2] Hp].
  { exists (rrefresh (hallvars (n2h_formula r (frl x A)))
                     (flat_map (fun C => hallvars (n2h_formula r C)) (subs x u A :: l)) r).
    - split; [ constructor; simpl | ].
      + apply (good_for_refresh _ (frl x A) _ (hallvars (n2h_formula r (frl x A)))).
        rewrite app_nil_r.
        now intros z Hz.
      + apply Forall_forall; intros C HC.
        apply (good_for_refresh_preserv (hallvars (n2h_formula r (frl x A)))).
        * intros z Hz.
          apply in_or_app; right.
          revert HC; clear - Hz; induction l; intros Hin; inversion Hin; subst; simpl.
          -- apply in_or_app; left.
             apply n2h_allvars; now apply in_or_app; left.
          -- apply IHl in H.
             now apply in_or_app; right.
        * intros z Hz; inversion Hz.
        * inversion H; subst.
          now apply Forall_forall with (x:=C) in H3.
      + apply good_for_refresh_preserv.
        * intros z Hz; apply in_or_app; left.
          apply n2h_allvars; now apply in_or_app; left.
        * intros z Hz; inversion Hz.
        * now inversion H.
    - remember (subs x u A) as B.
      apply good_for_hilbert_rrefresh.
      + intros z Hz; simpl.
        clear - Hz.
        revert B Hz; induction l; simpl; intros B Hz.
        * now apply in_or_app; left.
        * apply IHl in Hz.
          apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz].
          -- simpl in Hz; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [right|left]; auto.
             now apply in_or_app; left.
          -- right; now apply in_or_app; right.
      + clear - H.
        revert B H; induction l; intros B HF; inversion HF; subst; simpl; auto.
        inversion H2; subst.
        apply IHl; constructor; auto.
        now split. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply X ]; auto.
  rewrite n2h_subs with (lv:=x::nil); [ apply hprove_INST | | ].
  + apply lgood_hgood_closed with (lv := nil) (lv' := x :: nil); auto.
    * now constructor.
    * now inversion Hg1.
  + now constructor.
  + now inversion Hg1.
- auto.
- apply X.
  inversion H; destruct H2.
  now repeat constructor.
- remember (vfresh (flat_map (fun C => hallvars (n2h_formula r0 C)) (frl x A :: l))) as y.
  remember (rup (hvar y) r0) as r1.
  specialize X with r1.
  assert (Forall (rgood_for r1) (subs x (dvar 0) (fupz A) :: map fupz l)) as pi'.
  { revert Heqy; inversion H; subst; intros Heqy.
    constructor.
    - simpl in H2; apply good_for_rup_subs with (x:=x) (y:=y) in H2.
      + rewrite <- (app_nil_l _) in H2; now apply lgood_for_less in H2.
      + now constructor.
      + intros Heq; inversion Heq; auto; subst x.
        apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl y A :: l)).
        now left.
      + intros Hin.
        apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl x A :: l)).
        rewrite <- Heqy; simpl; right.
        now apply in_or_app; left.
    - apply Forall_forall; intros B HB.
      apply in_map_iff in HB.
      destruct HB as [C [Heq HC]]; subst.
      apply Forall_forall with (x:=C) in H3; auto.
      now apply good_for_rup. }
  apply X in pi'.
  apply hprove_GEN with (x:=y) in pi'.
  assert (hprove (n2h_sequent r1 (map fupz l) (frl y (subs x (tvar y) (fupz A))))) as pi''.
  { eapply hprove_MP; [ apply hprove_FRLsequent | ].
    - intros Hin.
      apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl x A :: l)).
      rewrite <- Heqy.
      simpl; apply in_cons.
      apply in_or_app; right.
      clear - Heqr1 Hin.
      revert Hin; induction l; simpl; intros Hin; auto.
      apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; auto.
      subst; rewrite n2h_rup in Hin.
      now apply hffreevars_hallvars.
    - enough (n2h_sequent r1 (map fupz l) (subs x (dvar 0) (fupz A))
            = n2h_sequent r1 (map fupz l) (subs x (tvar y) (fupz A))) as Heq
        by now rewrite <- Heq.
      remember (subs x (dvar 0) (fupz A)) as B.
      remember (subs x (tvar y) (fupz A)) as C.
      assert (n2h_formula r1 B = n2h_formula r1 C).
      { subst B C r1; clear; induction A; simpl; auto.
        - f_equal.
          rewrite ? map_map.
          apply map_ext; intros t.
          term_induction t.
        - f_equal; auto.
        - case_eq (beq_vat v x); intros Heq; auto; simpl.
          now rewrite IHA.
        - case_eq (beq_vat v x); intros Heq; auto; simpl.
          now rewrite IHA. }
      clear - H0; revert B C H0; induction l; simpl; intros B C Heq; auto.
      apply IHl; simpl; f_equal; auto. }
  remember (frl y (subs x (tvar y) (fupz A))) as B.
  remember (frl x A) as C.
  assert (hprove (n2h_formula r1 B ⟶ n2h_formula r0 C)) as pi'''.
  { subst B C; clear - H Heqr1 Heqy; simpl.
    eapply hprove_MP; [ apply hprove_FRL | ].
    + clear Heqy; simpl; intros Hin.
      apply in_remove in Hin; destruct Hin as [Hin Hneq].
      inversion H; subst.
      apply Hneq.
      revert Hin H2; clear; formula_induction A.
      * apply Forall_fold_right in H2.
        revert Hin H2; induction l; simpl; intros Hin HF; inversion HF; [inversion Hin | ]; subst.
        apply in_app_or in Hin; destruct Hin as [Hin|Hin].
        -- revert Hin H1; clear; term_induction a; intros Hin Hg.
           ++ inversion Hg; subst.
              now exfalso.
           ++ case_eq (beq_vat x0 x); intros Heq; rewrite Heq in Hin; simpl in Hin.
              ** now destruct Hin.
              ** exfalso; apply eqb_neq in Heq.
                 now destruct Hin.
           ++ apply Forall_fold_right in Hg.
              revert IHl Hin Hg; induction l; simpl; intros Hl Hin Hg.
              ** inversion Hin.
              ** inversion Hg; inversion Hl; subst.
                 apply in_app_or in Hin; destruct Hin as [Hin|Hin].
                 --- apply H5; auto.
                 --- apply IHl in H6; auto.
        -- apply IHl; auto.
      * apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
      * case_eq (beq_vat x0 x); intros Heq; rewrite Heq in Hin; simpl in Hin; apply in_remove in Hin; destruct Hin.
        -- exfalso; apply H0.
           now apply beq_eq_vat in Heq.
        -- apply IHA; auto.
           rewrite <- (app_nil_l _) in H2; now apply lgood_for_less in H2.
     * case_eq (beq_vat x0 x); intros Heq; rewrite Heq in Hin; simpl in Hin; apply in_remove in Hin; destruct Hin.
        -- exfalso; apply H0.
           now apply beq_eq_vat in Heq.
        -- apply IHA; auto.
           rewrite <- (app_nil_l _) in H2; now apply lgood_for_less in H2.
    + apply hprove_GEN.
      eapply hprove_CUT; [ apply hprove_INST with (t:=hvar x) | ]; simpl.
      * repeat constructor.
        assert (~ In y (hallvars (n2h_formula r1 (fupz A)))) as HA.
        { intros Hin.
          apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl x A :: l)).
          rewrite <- Heqy; simpl; right.
          apply in_or_app; left.
          now subst r1; rewrite n2h_rup in Hin. }
        revert HA; clear; formula_induction A.
        -- case_eq (beq_vat x0 x); intros Heq; simpl; intros Hin.
           ++ exfalso; apply H0.
              apply in_remove in Hin; destruct Hin.
              now apply hffreevars_hallvars.
           ++ apply eqb_neq in Heq.
              split; auto.
        -- case_eq (beq_vat x0 x); intros Heq; simpl; intros Hin.
           ++ exfalso; apply H0.
              apply in_remove in Hin; destruct Hin.
              now apply hffreevars_hallvars.
           ++ apply eqb_neq in Heq.
              split; auto.
      * enough (hfsubs y (hvar x) (n2h_formula r1 (subs x (tvar y) (fupz A))) = n2h_formula r0 A) as Heq
          by (rewrite Heq; apply hprove_I).
        rewrite n2h_subs with (lv:=x::nil); simpl.
        -- subst r1; rewrite n2h_rup.
           remember (n2h_formula r0 A) as B.
           assert (~ In y (hallvars B)) as HB.
           { intros Hin.
             apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (frl x A :: l)).
             rewrite <- Heqy.
             simpl; right.
             now subst; apply in_or_app; left. }
           revert HB; clear; hformula_induction B.
           ++ assert (~ In y (hfreevars t)) by (intros Hin; apply HB; simpl; now apply in_or_app; left).
              revert H; clear; hterm_induction t; intros Hin.
              ** case_eq (beq_vat x0 x); intros Heq; simpl.
                 --- rewrite eqb_refl.
                     now apply beq_eq_vat in Heq; subst.
                 --- assert (x0 <> y) as Hneq by (intros Heq'; apply Hin; auto).
                     apply eqb_neq in Hneq; rewrite Hneq; auto.
              ** f_equal.
                 rewrite <- (map_id l) at 2.
                 apply map_ext_in; intros z Hz.
                 apply Forall_forall with (x:=z) in IHl; auto.
                 apply IHl.
                 intros Hinz; apply Hin.
                 revert Hz Hinz; clear; induction l; intros Hz Hinz; inversion Hz; subst; simpl.
                 --- now apply in_or_app; left.
                 --- apply in_or_app; right.
                     now apply IHl.
           ++ apply HB; simpl.
              now apply in_or_app; right.
           ++ case_eq (beq_vat x0 x); intros Heq.
              ** apply nfree_hfsubs; simpl.
                 intros Hin; apply H0.
                 apply in_remove in Hin.
                 destruct Hin; now apply hffreevars_hallvars.
              ** simpl; case_eq (beq_vat x0 y); intros Heq2; f_equal; auto.
                 exfalso; apply H.
                  now apply beq_eq_vat.
           ++ case_eq (beq_vat x0 x); intros Heq.
              ** apply nfree_hfsubs; simpl.
                 intros Hin; apply H0.
                 apply in_remove in Hin.
                 destruct Hin; now apply hffreevars_hallvars.
              ** simpl; case_eq (beq_vat x0 y); intros Heq2; f_equal; auto.
                 exfalso; apply H.
                  now apply beq_eq_vat.
         -- now constructor.
         -- subst r1; apply good_for_rup.
            now inversion H. }
  clear - Heqr1 pi'' pi'''.
  revert B C pi''' pi''; induction l; simpl; intros B C pBC pi.
  + eapply hprove_MP; eassumption.
  + apply IHl with (imp (fupz a) B); auto; simpl.
    subst r1; rewrite n2h_rup.
    eapply hprove_MP; [ apply hprove_B | apply pBC ].
- assert ({rf : _ & Forall (rgood_for rf) (exs x A :: l) /\ rgood_for rf (subs x u A)
                  & hprove (n2h_sequent rf l (exs x A)) -> hprove (n2h_sequent r0 l (exs x A))})
    as [rf [Hg1 Hg2] Hp].
  { exists (rrefresh (hallvars (n2h_formula r0 (subs x u A)))
                     (flat_map (fun C => hallvars (n2h_formula r0 C)) (exs x A :: l)) r0).
    - split; [ constructor; simpl | ].
      + apply good_for_refresh_preserv.
        * intros z Hz; right; apply in_or_app; left.
          apply n2h_allvars; now apply in_or_app; left.
        * intros z Hz; inversion Hz; [ now  constructor | now apply in_cons ].
        * now inversion H.
      + apply Forall_forall; intros C HC.
        apply (good_for_refresh_preserv (hallvars (n2h_formula r0 (subs x u A)))).
        * intros z Hz.
          right; apply in_or_app; right.
          revert HC; clear - Hz; induction l; intros Hin; inversion Hin; subst; simpl.
          -- apply in_or_app; left.
             apply n2h_allvars; now apply in_or_app; left.
          -- apply IHl in H.
             now apply in_or_app; right.
        * intros z Hz; inversion Hz.
        * inversion H; subst.
          now apply Forall_forall with (x:=C) in H3.
      + apply (good_for_refresh _ (subs x u A) _ (hallvars (n2h_formula r0 (subs x u A)))).
        rewrite app_nil_r.
        now intros z Hz.
    - remember (exs x A) as B.
      apply good_for_hilbert_rrefresh.
      + intros z Hz; simpl.
        clear - Hz.
        revert B Hz; induction l; simpl; intros B Hz.
        * now rewrite app_nil_r.
        * apply IHl in Hz.
          apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz].
          -- simpl in Hz; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [right|left]; auto.
             now apply in_or_app; left.
          -- right; now apply in_or_app; right.
      + clear - H.
        revert B H; induction l; intros B HF; inversion HF; subst; simpl; auto.
        inversion H2; subst.
        apply IHl; constructor; auto.
        now split. }
  apply Hp.
  eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Bsequent | ] | apply X ]; auto.
  + rewrite n2h_subs with (lv:=x::nil); [ apply hprove_EINST | | ].
    * apply lgood_hgood_closed with (lv := nil) (lv' := x :: nil); auto.
      -- now constructor.
      -- now inversion Hg1.
    * now constructor.
    * now inversion Hg1.
  + inversion Hg1; now constructor.
- remember (rrefresh (hallvars (n2h_formula r0 (exs x A)))
                     (flat_map (fun C => hallvars (n2h_formula r0 C)) (C :: l)) r0) as r1.
  assert (Forall (rgood_for r1) (C :: l)) as HgCl1.
  { remember (C :: l) as l'.
    remember (flat_map (fun C : formula => hallvars (n2h_formula r0 C)) l') as lv.
    assert (incl lv lv) as Hincl by (now intros z Hz).
    rewrite Heqlv in Hincl at 1.
    clear - lv H Hincl Heqr1.
    revert H Hincl; induction l'; simpl; intros Hg Hincl; constructor;
      revert Heqr1; inversion Hg; subst; intros Heqr1.
    - subst; apply good_for_refresh_preserv; auto.
      + intros z Hz; apply Hincl.
        apply in_or_app; left.
        apply n2h_allvars.
        now apply in_or_app; left.
      + intros z Hz; inversion Hz.
    - apply IHl'; auto.
      intros z Hz; apply Hincl.
      now apply in_or_app; right. }
  assert (rgood_for r1 C) as HgC1 by (now inversion HgCl1).
  assert (Forall (rgood_for r1) l) as Hgl1 by (now inversion HgCl1); clear HgCl1.
  assert (rgood_for r1 (exs x A)) as HgA1
    by (subst; apply good_for_refresh; rewrite app_nil_r; now intros z Hz).
  apply good_for_hilbert_rrefresh with (l:=hallvars (n2h_formula r0 (exs x A)))
                                       (ld:=flat_map (fun C : formula => hallvars (n2h_formula r0 C)) (C :: l)).
  + clear; revert C; induction l; simpl; intros C.
    * rewrite app_nil_r; now intros z Hz.
    * intros z Hz; apply IHl in Hz; simpl in Hz.
      apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz].
      -- apply in_app_or in Hz; destruct Hz as [Hz|Hz]; auto.
         right; now apply in_or_app; left.
      -- right; now apply in_or_app; right.
  + clear - H; revert C H; induction l; simpl; intros C Hg; inversion Hg; subst; auto.
    inversion H2; subst.
    apply IHl; constructor; simpl; auto.
  + rewrite <- Heqr1.
    eapply hprove_MP; [ eapply hprove_MP; [ apply hprove_Ssequent | ] | apply X; constructor; auto ].
    apply hprove_imp_sequent.
    remember (vfresh (flat_map (fun C => hallvars (n2h_formula r1 C)) (exs x A :: C :: l))) as y.
    assert (hprove (hexs x (n2h_formula r1 A) ⟶ hexs y (hfsubs x (hvar y) (n2h_formula r1 A)))) as pi'.
    { simpl in Heqy.
      remember (n2h_formula r1 A) as B; clear - Heqy.
      assert (~ In y (hallvars B)) as Hf.
      { intros Hin.
        apply vfresh_prop with (x:: hallvars B ++
             hallvars (n2h_formula r1 C) ++ flat_map (fun C : formula => hallvars (n2h_formula r1 C)) l).
        rewrite <- Heqy; simpl; right.
        now apply in_or_app; left. }
      clear Heqy.
      eapply hprove_MP; [ apply hprove_EXS | ].
      - simpl; intros Hin.
        apply in_remove in Hin; destruct Hin as [Hin _].
        apply hffreevars_subs in Hin; destruct Hin as [Hin|Hin].
        + simpl in Hin; destruct Hin as [Heq Hin]; destruct Heq; auto; subst.
          now apply Hf, hffreevars_hallvars.
        + now destruct Hin.
      - apply hprove_GEN.
        replace (B ⟶ hexs y (hfsubs x (hvar y) B))
           with (hfsubs y (hvar x) (hfsubs x (hvar y) B) ⟶ hexs y (hfsubs x (hvar y) B)).
        + apply hprove_EINST.
          simpl; repeat constructor.
          revert Hf; formula_induction B.
          * case_eq (beq_vat x0 x); simpl; intros Heq Hin.
            -- exfalso.
               apply in_remove in Hin; destruct Hin.
               apply H0, hffreevars_hallvars; assumption.
            -- apply eqb_neq in Heq; split; auto.
          * case_eq (beq_vat x0 x); simpl; intros Heq Hin.
            -- exfalso.
               apply in_remove in Hin; destruct Hin.
               apply H0, hffreevars_hallvars; assumption.
            -- apply eqb_neq in Heq; split; auto.
        + f_equal.
          now apply hbisubs. }
    simpl; eapply hprove_CUT; [ apply pi' | ].
    eapply hprove_MP; [ apply hprove_EXS | ].
    * intros Hin.
      apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r1 C)) (exs x A :: C :: l)).
      rewrite <- Heqy.
      simpl; right; apply in_or_app; right.
      clear - Hin; revert C Hin; induction l; simpl; intros C Hin.
      -- rewrite app_nil_r; apply n2h_allvars.
         now apply in_or_app; right.
      -- apply IHl in Hin; simpl in Hin.
         apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
         ++ apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
            right; now apply in_or_app; left.
         ++ right; now apply in_or_app; right.
    * apply hprove_GEN.
      replace (hvar y) with (n2h_term r1 (tvar y)) by reflexivity.
      rewrite <- n2h_subs with (lv:=x::nil); auto; [ | now constructor ].
      apply hprove_sequent_imp.
      remember (rup (hvar y) r1) as r2.
      assert (Forall (rgood_for r2) (fupz C :: subs x (dvar 0) (fupz A) :: map fupz l)) as pi.
      { constructor; [ | constructor ]; subst r2.
        - now apply good_for_rup.
        - simpl in HgA1; apply good_for_rup_subs with (x:=x) (y:=y) in HgA1.
          + rewrite <- (app_nil_l _) in HgA1; now apply lgood_for_less in HgA1.
          + now constructor.
          + intros Heq; inversion Heq; auto; subst x.
            apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r1 C)) (exs y A :: C :: l)).
            now left.
          + intros Hin.
            apply vfresh_prop with (flat_map (fun C : formula => hallvars (n2h_formula r1 C)) (exs x A :: C :: l)).
            rewrite <- Heqy; simpl; right.
            now apply in_or_app; left.
        - apply Forall_forall; intros E HE.
          apply in_map_iff in HE; destruct HE as [E' [Heq HE]]; subst E.
          apply Forall_forall with (x:=E') in Hgl1; auto.
          now apply good_for_rup. }
      apply X0 in pi; simpl in pi.
      remember (imp (subs x (dvar 0) (fupz A)) (fupz C)) as B.
      remember (imp (subs x (tvar y) A) C) as D.
      assert (hprove (n2h_formula r2 B ⟶ n2h_formula r1 D)) as HBD.
      { subst B D r2; simpl; rewrite ? n2h_rup.
        rewrite n2h_rup_subs with (lv:=x::nil); auto.
        - enough (n2h_formula r1 (subs x (tvar y) A) = hfsubs x (hvar y) (n2h_formula r1 A))
            as Heq by (rewrite Heq; apply hprove_I).
          apply n2h_subs with (x :: nil); auto.
          now constructor.
        - now constructor. }
      clear - Heqr2 pi HBD; revert B D pi HBD; induction l; simpl; intros B D pi HBD.
      -- eapply hprove_MP; eassumption.
      -- apply IHl with (imp (fupz a) B); auto.
         simpl; subst.
         rewrite n2h_rup.
         eapply hprove_MP; [ apply hprove_B | apply HBD ].
Qed.

Proposition n2h_closed : forall r, (forall n, hclosed (r n)) ->
  forall A, prove nil A -> hprove (n2h_formula r A).
Proof.
intros r Hc A pi.
apply normalization in pi.
change (n2h_formula r A) with (n2h_sequent r nil A).
apply n2h; [ assumption | ].
apply Forall_forall; intros.
now apply lgood_for_closed.
Qed.

