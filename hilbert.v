(* Hilbert system for Intuitionistic Logic with implication *)

Require Import PeanoNat.
Require Import List.






(* TODO move *)

Lemma Forall_and {A} : forall (P Q : A -> Prop),
    forall l, Forall (fun x => P x /\ Q x) l -> Forall P l /\ Forall Q l.
Proof.
induction l; intros HF.
- split; constructor.
- inversion HF; subst.
  apply IHl in H2.
  destruct H1 as [HPa HQa]; destruct H2 as [HP HQ].
  now split; constructor.
Qed.

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













Tactic Notation "rnow" tactic(t) :=
  t ; simpl ; autorewrite with core in * ; simpl ; intuition.
Tactic Notation "rnow" tactic(t) "then" tactic(t1) :=
  t ; simpl ; autorewrite with core in * ; simpl ; intuition t1 ; simpl ; intuition.



(** * Atoms *)

Parameter fatom : Type. (* function symbols for [term] *)
Parameter hatom : Type. (* variables for quantification *)
Parameter beq_hat : hatom -> hatom -> bool. (* boolean equality on [hatom] *)
Parameter beq_eq_hat : forall a b, beq_hat a b = true <-> a = b.
   (* equality specification for [hatom] *)

(* [vatom] presented as a type with Boolean equality *)
Module hatomBoolEq <: Equalities.UsualBoolEq.
Definition t := hatom.
Definition eq := @eq hatom.
Definition eqb := beq_hat.
Definition eqb_eq := beq_eq_hat.
End hatomBoolEq.
Module hatomEq := Equalities.Make_UDTF hatomBoolEq.
Module hatomFacts := Equalities.BoolEqualityFacts hatomEq.
Export hatomFacts.

Ltac case_analysis :=
match goal with
| |- context f [?x =? ?y] => case_eq (x =? y)
| |- context f [beq_hat ?x ?y] => case_eq (beq_hat x y)
| |- context f [hatomEq.eq_dec ?x ?y] => case_eq (hatomEq.eq_dec x y)
end.
Ltac rcauto := simpl ; autorewrite with core in * ; simpl ; rnow case_analysis.

(** * First-Order Terms *)

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
Inductive hterm :=
| hvar : hatom -> hterm
| hconstr : fatom -> list hterm -> hterm.

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
| hvar y => if (beq_hat y x) then u else hvar y
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
Hint Resolve hclosed_nohfreevars.

Lemma nfree_htsubs : forall x u t, ~ In x (hfreevars t) -> htsubs x u t = t.
Proof. hterm_induction t; try rcauto; intros Heq.
- assert (beq_hat x0 x = false) as Hb.
  { case_eq (beq_hat x0 x); [ intros Heq2 | reflexivity ].
    exfalso; apply Heq; left.
    now apply beq_eq_hat. }
  now rewrite Hb.
- f_equal ; revert IHl Heq ; induction l ; intros; [ reflexivity | ].
  inversion IHl0 ; subst.
  simpl in Heq; simpl; rewrite H1; [ f_equal | ].
  + apply IHl; [ assumption | ].
    intros Hf; apply Heq, in_or_app; now right.
  + intros Hf; apply Heq, in_or_app; now left.
Qed.
Hint Rewrite nfree_htsubs using try (intuition ; fail) ;
                               (try apply hclosed_nohfreevars) ; intuition ; fail.

Lemma htsubs_htsubs_com : forall x v y u, beq_hat x y = false -> ~ In x (hfreevars u) -> forall t,
  htsubs y u (htsubs x v t) = htsubs x (htsubs y u v) (htsubs y u t).
Proof. hterm_induction t.
rnow case_eq (beq_hat x0 x) ; case_eq (beq_hat x0 y) then try rewrite H1 ; try rewrite H2.
exfalso.
now rewrite eqb_neq in H ; rewrite beq_eq_hat in H1 ; rewrite beq_eq_hat in H2 ; subst.
Qed.
Hint Rewrite htsubs_htsubs_com using try (intuition ; fail) ;
                                    (try apply hclosed_nohfreevars) ; intuition ; fail.



(* Formulas *)

Parameter hfatom : Type.  (* relation symbols for [formula] *)

(** formulas *)
(** first-order formulas in the langage: implication, universal quantification *)
Inductive hformula :=
| hfvar : hfatom -> list hterm -> hformula
| himp : hformula -> hformula -> hformula
| hfrl : hatom -> hformula -> hformula.

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
  induction A as [ XX ll | A1 A2 | xx A ] ; simpl ; intros ;
  [ try f_equal ; try (induction ll as [ | tt lll IHll ] ; simpl ; intuition ;
                       rewrite IHll ; f_equal ; intuition)
  | try (f_equal ; intuition)
  | try (f_equal ; intuition) ] ; try ((rnow idtac) ; fail) ; try (rcauto ; fail).

Fixpoint hfsize A :=
match A with
| hfvar _ _ => 1
| himp B C => S (hfsize B + hfsize C)
| hfrl _ B => S (hfsize B)
end.

Fixpoint hffreevars A :=
match A with
| hfvar _ l => concat (map hfreevars l)
| himp B C => (hffreevars B) ++ (hffreevars C)
| hfrl x B => remove hatomEq.eq_dec x (hffreevars B)
end.

Fixpoint hgood_for x y A :=
match A with
| hfvar X l => True
| himp B C => hgood_for x y B /\ hgood_for x y C
| hfrl z B => hgood_for x y B /\ (y <> z \/ ~ In x (hffreevars (hfrl z B)))
end.
(*
Fixpoint hbinds_for x y A :=
match A with
| hfvar X l => False
| himp B C => hbinds_for x y B \/ hbinds_for x y C
| hfrl z B => hbinds_for x y B \/ (y = z /\ In x (hffreevars (hfrl z B)))
end.
*)

(** substitutes [hterm] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint hfsubs x u A :=
match A with
| hfvar X l => hfvar X (map (htsubs x u) l)
| himp B C => himp (hfsubs x u B) (hfsubs x u C)
| hfrl y B as C => if (beq_hat y x) then C else hfrl y (hfsubs x u B)
end.

Lemma hfsize_subs : forall u x A, hfsize (hfsubs x u A) = hfsize A.
Proof. hformula_induction A. Qed.
Hint Rewrite hfsize_subs.

Inductive hprove : hformula -> Type :=
| hprove_K : forall A B, hprove (A ⟶ B ⟶ A)
| hprove_S : forall A B C, hprove ((A ⟶ B ⟶ C) ⟶ ((A ⟶ B) ⟶ A ⟶ C))
| hprove_MP : forall A B, hprove (A ⟶ B) -> hprove A -> hprove B
| hprove_INST : forall x A t, Forall (fun y => hgood_for x y A) (hfreevars t) ->
                   hprove (hfrl x A ⟶ hfsubs x t A)
| hprove_FRL : forall x A B, ~ In x (hffreevars A) -> hprove ((hfrl x (A ⟶ B)) ⟶ A ⟶ hfrl x B)
| hprove_GEN : forall x A, hprove A -> hprove (hfrl x A).

Lemma hprove_I : forall A, hprove (A ⟶ A).
Proof.
intros A.
eapply hprove_MP.
- eapply hprove_MP.
  + apply hprove_S.
  + apply hprove_K with (B := A ⟶ A).
- apply hprove_K.
Qed.

Lemma hprove_B : forall A B C, hprove ((B ⟶ C) ⟶ ((A ⟶ B) ⟶ A ⟶ C)).
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







Require Import fot nj1.

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
| frl z B => good_for x y B /\ (y <> z \/ ~ In x (ffreevars (frl z B)))
| exs z B => good_for x y B /\ (y <> z \/ ~ In x (ffreevars (exs z B)))
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
      simpl in Hb; destruct Hb as [Hb [Hneq | Hf]].
      -- now apply Hneq.
      -- apply Hf.
         apply eqb_neq in Heq2.
         apply notin_remove; [ | assumption ].
         now intros Heq; apply Heq2.
    * now rewrite 2 nfree_subs.
    * now rewrite nfree_tsubs; [ reflexivity | ].
  + apply IHA.
    apply Forall_forall; intros z Hinz.
    apply Forall_forall with (x:=z) in Hb; [ | assumption ].
    apply Hb.
- simpl; case_eq (beq_vat v0 x) ; case_eq (beq_vat v0 y); intros Heq1 Heq2; simpl; rewrite Heq1, Heq2;
    try reflexivity; f_equal.
  + apply beq_eq_vat in Heq1; subst.
    destruct (in_dec vatomEq.eq_dec y (freevars v)); [ destruct (in_dec vatomEq.eq_dec x (ffreevars A)) | ].
    * exfalso.
      apply Forall_forall with (x:=y) in Hb; [ | assumption ].
      simpl in Hb; destruct Hb as [Hb [Hneq | Hf]].
      -- now apply Hneq.
      -- apply Hf.
         apply eqb_neq in Heq2.
         apply notin_remove; [ | assumption ].
         now intros Heq; apply Heq2.
    * now rewrite 2 nfree_subs.
    * now rewrite nfree_tsubs; [ reflexivity | ].
  + apply IHA.
    apply Forall_forall; intros z Hinz.
    apply Forall_forall with (x:=z) in Hb; [ | assumption ].
    apply Hb.
Qed.

(*
Fixpoint binds_for x y A :=
match A with
| var X l => False
| imp B C => binds_for x y B \/ binds_for x y C
| frl z B => binds_for x y B \/ (y = z /\ In x (ffreevars (frl z B)))
| exs z B => binds_for x y B \/ (y = z /\ In x (ffreevars (exs z B)))
end.
*)








Lemma hfreevars_tsubs_closed : forall x u, hclosed u -> forall t,
  hfreevars (htsubs x u t) = remove hatomEq.eq_dec x (hfreevars t).
Proof. hterm_induction t.
- case_eq (beq_hat x0 x); intros Heq.
  + apply beq_eq_hat in Heq; subst.
    now destruct (hatomEq.eq_dec x x); [ | exfalso; apply n ].
  + apply hatomFacts.eqb_neq in Heq.
    destruct (hatomEq.eq_dec x x0).
    * exfalso; now apply Heq.
    * reflexivity.
- revert IHl; induction l; simpl; intros Hl; [ reflexivity | ].
  inversion Hl; subst.
  rewrite IHl; simpl; [ | assumption ].
  now rewrite remove_app; f_equal.
Qed.

Lemma hfreevars_tsubs : forall x y u t, In x (hfreevars (htsubs y u t)) ->
  In x (hfreevars u) \/ In x (hfreevars t).
Proof.
hterm_induction t.
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

Lemma hfreevars_to_tsubs : forall t a x u,
  In x (hfreevars t) -> In a (hfreevars u) -> In a (hfreevars (htsubs x u t)).
Proof. hterm_induction t; intros a y u Hin1 Hin2.
- destruct Hin1 as [Hin1|Hin1]; [ | inversion Hin1 ].
  now apply beq_eq_hat in Hin1; rewrite Hin1.
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
- apply Forall_and in H; destruct H as [Hl Hr].
  apply in_or_app; apply in_app_or in H0; destruct H0 as [Hin|Hin]; [ left | right ].
  + now apply A1.
  + now apply IHA1.
- case_eq (beq_hat x x0); intros Heq; simpl.
  + exfalso.
    apply beq_eq_hat in Heq; subst.
    now apply remove_In in H0.
  + case_eq (beq_hat a x); intros Heq2.
    * exfalso.
      apply beq_eq_hat in Heq2; subst.
      apply hatomFacts.eqb_neq in Heq.
      apply in_remove in H0.
      apply Forall_forall with (x:=x) in H; [ | assumption ].
      destruct H as [_ [HF|HF]]; [ now apply HF | apply HF ].
      apply notin_remove; [ now intros Heq2; apply Heq | apply H0 ].
    * apply hatomFacts.eqb_neq in Heq2.
      apply notin_remove; [ assumption | ].
      apply IHA; try assumption.
      -- now apply Forall_and in H.
      -- apply hatomFacts.eqb_neq in Heq.
         now apply in_remove in H0.
Qed.






(* From Hilbert to Natural Deduction *)

Import EqNotations.
Axiom h2n_funat : fatom = tatom.
Axiom h2n_at : hatom = vatom.
Axiom h2n_fat : hfatom = atom.

Lemma beq_hat_vat : forall x0 x, beq_hat x0 x = beq_vat (rew [id] h2n_at in x0) (rew [id] h2n_at in x).
Proof.
intros x0 x.
case_eq (beq_hat x0 x); intros Heq.
- apply beq_eq_hat in Heq; subst.
  now symmetry; apply beq_eq_vat.
- apply hatomFacts.eqb_neq in Heq.
  symmetry; apply vatomFacts.eqb_neq.
  intros Heq2; apply Heq.
  rewrite <- (rew_opp_l id h2n_at x0).
  rewrite Heq2.
  now rewrite rew_opp_l.
Qed.

Fixpoint h2n_term t :=
match t with
| hvar x => tvar (rew [id] h2n_at in x)
| hconstr f l => tconstr (rew [id] h2n_funat in f) (map h2n_term l)
end.


Lemma h2n_freevars : forall t, freevars (h2n_term t) = map (fun x => rew [id] h2n_at in x) (hfreevars t).
Proof.
hterm_induction t.
revert IHl; induction l; simpl; intros Hl; [ reflexivity | ].
rewrite map_app.
inversion Hl; subst.
now rewrite IHl; f_equal.
Qed.

Lemma h2n_closed : forall t, hclosed t <-> closed (h2n_term t).
Proof.
intros t; rewrite h2n_freevars; destruct (hfreevars t); simpl; split; intros Heq; try reflexivity;
  inversion Heq.
Qed.

Lemma h2n_tsubs : forall x u t,
  h2n_term (htsubs x u t) = tsubs (rew [id] h2n_at in x) (h2n_term u) (h2n_term t).
Proof. hterm_induction t; rewrite <- beq_hat_vat; now case_eq (beq_hat x0 x); intros Heqb. Qed.

Lemma h2n_tup : forall k t, tup k (h2n_term t) = h2n_term t.
Proof. hterm_induction t. Qed.


Fixpoint h2n_formula A :=
match A with
| hfvar X l => var (rew [id] h2n_fat in X) (map h2n_term l)
| himp B C => imp (h2n_formula B) (h2n_formula C)
| hfrl y B => frl (rew [id] h2n_at in y) (h2n_formula B)
end.

Lemma h2n_ffreevars : forall A, ffreevars (h2n_formula A) = map (fun x => rew [id] h2n_at in x) (hffreevars A).
Proof.
hformula_induction A; try rewrite map_app; f_equal; try assumption.
- apply h2n_freevars.
- rewrite IHA.
  remember (hffreevars A) as l; clear; induction l; simpl; [ reflexivity | ].
  case_eq (vatomEq.eq_dec (rew [id] h2n_at in x) (rew [id] h2n_at in a)); intros; simpl.
  + rewrite IHl; f_equal.
    case_eq (hatomEq.eq_dec x a); intros; subst; [ reflexivity | exfalso ].
    apply n.
    rewrite <- (rew_opp_l id h2n_at x); rewrite e; now rewrite rew_opp_l.
  + rewrite IHl.
    now case_eq (hatomEq.eq_dec x a); intros; subst; [ exfalso | reflexivity ].
Qed.

Lemma h2n_fclosed : forall A, hffreevars A = nil <-> ffreevars (h2n_formula A) = nil.
Proof.
intros A; rewrite h2n_ffreevars; destruct (hffreevars A); simpl; split; intros Heq; try reflexivity;
  inversion Heq.
Qed.

Lemma h2n_fsubs : forall x u A,
  h2n_formula (hfsubs x u A) = subs (rew [id] h2n_at in x) (h2n_term u) (h2n_formula A).
Proof. hformula_induction A.
- apply h2n_tsubs.
- rewrite <- beq_hat_vat.
  now case_eq (beq_hat x0 x); intros Heqb; simpl; [ | rewrite IHA ].
Qed.

Lemma h2n_fup : forall k A, fup k (h2n_formula A) = h2n_formula A.
Proof. hformula_induction A; apply h2n_tup. Qed.

Lemma h2n_remove : forall x l,
   map (fun y => rew <- [id] h2n_at in y) (remove vatomEq.eq_dec (rew [id] h2n_at in x) l)
 = remove hatomEq.eq_dec x (map (fun y => rew <- [id] h2n_at in y) l).
Proof.
induction l; simpl; [ reflexivity | ].
destruct (vatomEq.eq_dec (rew [id] h2n_at in x) a); subst; simpl.
- rewrite ? rew_opp_l.
  now destruct (hatomEq.eq_dec x x); [ subst | now exfalso ].
- destruct (hatomEq.eq_dec x (rew <- [id] h2n_at in a));
    [ exfalso; now apply n; subst; rewrite rew_opp_r | ].
  now f_equal.
Qed.

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
    * destruct Hb as [Hb [nHneq | Hf]].
      -- now split; [ apply IHA | left ].
      -- split; [ now apply IHA | right ].
         enough (In x (ffreevars (subs v0 t A)) -> In x (ffreevars A)) as Himp.
         { intros Hin.
           apply in_remove in Hin; destruct Hin as [Hin Hneq].
           apply Himp in Hin.
           apply notin_remove with vatomEq.eq_dec (ffreevars A) x v in Hin; [ | assumption ].
           now revert Hin. }
         intros Hin; apply ffreevars_subs in Hin.
         destruct Hin as [Hin|Hin].
         ++ rewrite Hc in Hin; inversion Hin.
         ++ assumption.
  + case_eq (beq_vat v v0); intros Heq2; simpl.
    * assumption.
    * destruct Hb as [Hb [nHneq | Hf]].
      -- now split; [ apply IHA | left ].
      -- split; [ now apply IHA | right ].
         enough (In x (ffreevars (subs v0 t A)) -> In x (ffreevars A)) as Himp.
         { intros Hin.
           apply in_remove in Hin; destruct Hin as [Hin Hneq].
           apply Himp in Hin.
           apply notin_remove with vatomEq.eq_dec (ffreevars A) x v in Hin; [ | assumption ].
           now revert Hin. }
         intros Hin; apply ffreevars_subs in Hin.
         destruct Hin as [Hin|Hin].
         ++ rewrite Hc in Hin; inversion Hin.
         ++ assumption.
Qed.

(*
Lemma multi_subs_subs : forall L x v, ~ In x (map fst L) ->
  Forall (fun z : term => closed z) (map snd L) ->
  forall A, Forall (fun y => good_for x y A) (freevars v) ->
  multi_subs L (subs x v A) = subs x (multi_tsubs L v) (multi_subs L A).
Proof.
induction L; simpl; intros x v Hin Hc A Hb; [ reflexivity | ].
destruct a; simpl; simpl in Hc, Hin; inversion Hc; subst.
rewrite <- IHL; try assumption.
- f_equal; apply subs_subs_com_good; try assumption.
  apply eqb_neq; intros Heq; apply Hin; now left.
- intros Hin2; apply Hin; now right.
- apply Forall_forall; intros z Hinz.
  apply freevars_tsubs in Hinz.
  destruct Hinz as [Hinz|Hinz].
  { exfalso; rewrite H1 in Hinz; inversion Hinz. }
  apply Forall_forall with (x := z) in Hb; [ | assumption ].
  assert (v0 <> x) as Heq by (intros Heq; apply Hin; now left).
  revert H1 Hb Heq; clear; induction A; simpl; intros Hc Hb Heq.
  + constructor.
  + now destruct Hb as [Hb1 Hb2]; split; [ apply IHA1 | apply IHA2 ].
  + case_eq (beq_vat v v0); intros Heq2; simpl.
    * assumption.
    * destruct Hb as [Hb [nHneq | Hf]].
      -- now split; [ apply IHA | left ].
      -- split; [ now apply IHA | right ].
         enough (In x (ffreevars (subs v0 t A)) -> In x (ffreevars A)) as Himp.
         { intros Hin.
           apply in_remove in Hin; destruct Hin as [Hin Hneq].
           apply Himp in Hin.
           apply notin_remove with vatomEq.eq_dec (ffreevars A) x v in Hin; [ | assumption ].
           now revert Hin. }
         intros Hin; apply ffreevars_subs in Hin.
         destruct Hin as [Hin|Hin].
         ++ rewrite Hc in Hin; inversion Hin.
         ++ assumption.
  + case_eq (beq_vat v v0); intros Heq2; simpl.
    * assumption.
    * destruct Hb as [Hb [nHneq | Hf]].
      -- now split; [ apply IHA | left ].
      -- split; [ now apply IHA | right ].
         enough (In x (ffreevars (subs v0 t A)) -> In x (ffreevars A)) as Himp.
         { intros Hin.
           apply in_remove in Hin; destruct Hin as [Hin Hneq].
           apply Himp in Hin.
           apply notin_remove with vatomEq.eq_dec (ffreevars A) x v in Hin; [ | assumption ].
           now revert Hin. }
         intros Hin; apply ffreevars_subs in Hin.
         destruct Hin as [Hin|Hin].
         ++ rewrite Hc in Hin; inversion Hin.
         ++ assumption.
Qed.
*)

(*
Lemma multi_subs_subs : forall A L x v, ~ In x (map fst L) ->
  Forall (fun z : term => closed z) (map snd L) -> closed v ->
  multi_subs L (subs x v A) = subs x (multi_tsubs L v) (multi_subs L A).
Proof. formula_induction A.
- simpl; rewrite 2 multi_subs_var; simpl; f_equal.
  rewrite 2 map_map; apply map_ext.
  apply multi_tsubs_tsubs; [ assumption | ].
  revert H0; clear; induction L; constructor; inversion H0; subst.
  + rewrite H2; intros Hin; inversion Hin.
  + now apply IHL.
- now simpl; rewrite 2 multi_subs_imp; rewrite A1, IHA1; simpl.
- simpl; rewrite multi_subs_frl.
  case_eq (beq_vat x x0); intros Heq; simpl; rewrite Heq; rewrite multi_subs_frl; try reflexivity; f_equal.
  rewrite IHA; try assumption; f_equal.
  + now rewrite 2 multi_tsubs_closed.
  + apply eqb_neq in Heq.
   intros Hin; apply H; revert Heq Hin; clear; induction L; simpl; intros Hneq Hin.
   * assumption.
   * destruct a; simpl in Hin; simpl.
     case_eq (beq_vat x v); intros Heq; rewrite Heq in Hin.
     -- right; now apply IHL.
     -- now inversion Hin; [ left | right; apply IHL ].
  + revert H0; clear; induction L; intros HF; simpl.
    * constructor.
    * destruct a; simpl; simpl in HF; inversion HF; subst.
      case_eq (beq_vat x v); intros Heq.
      -- now apply IHL.
      -- simpl; constructor; try assumption.
         now apply IHL.
- simpl; rewrite multi_subs_exs.
  case_eq (beq_vat x x0); intros Heq; simpl; rewrite Heq; rewrite multi_subs_exs; try reflexivity; f_equal.
  rewrite IHA; try assumption; f_equal.
  + now rewrite 2 multi_tsubs_closed.
  + apply eqb_neq in Heq.
   intros Hin; apply H; revert Heq Hin; clear; induction L; simpl; intros Hneq Hin.
   * assumption.
   * destruct a; simpl in Hin; simpl.
     case_eq (beq_vat x v); intros Heq; rewrite Heq in Hin.
     -- right; now apply IHL.
     -- now inversion Hin; [ left | right; apply IHL ].
  + revert H0; clear; induction L; intros HF; simpl.
    * constructor.
    * destruct a; simpl; simpl in HF; inversion HF; subst.
      case_eq (beq_vat x v); intros Heq.
      -- now apply IHL.
      -- simpl; constructor; try assumption.
         now apply IHL.
Qed.
*)

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
  incl (hffreevars A) (map (fun z => rew <- [id] h2n_at in fst z) L) ->
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
    rewrite <- (rew_opp_r id h2n_at z) in Hinz.
    unfold incl in Hincl; specialize Hincl with (rew <- [id] h2n_at in z).
    assert (In (rew <- [id] h2n_at in z) (hffreevars A)) as HA.
    { remember (hffreevars A) as l; clear - Hinz.
      rewrite <- (rew_opp_r id h2n_at z).
      apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hinz.
      rewrite map_map in Hinz.
      assert (map (fun x => rew <- [id] h2n_at in rew [id] h2n_at in x) l = l).
      { rewrite <- (map_id l); rewrite map_map.
        apply map_ext; intros a; now rewrite rew_opp_l. }
      now rewrite H in Hinz. }
    apply Hincl in HA; inversion HA.
  + rewrite h2n_ffreevars in Hinz.
    rewrite <- (rew_opp_r id h2n_at z) in Hinz.
    unfold incl in Hincl; specialize Hincl with (rew <- [id] h2n_at in z).
    assert (In (rew <- [id] h2n_at in z) (hffreevars A)) as HA.
    { remember (hffreevars A) as l; clear - Hinz.
      rewrite <- (rew_opp_r id h2n_at z).
      apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hinz.
      rewrite map_map in Hinz.
      assert (map (fun x => rew <- [id] h2n_at in rew [id] h2n_at in x) l = l).
      { rewrite <- (map_id l); rewrite map_map.
        apply map_ext; intros a; now rewrite rew_opp_l. }
      now rewrite H in Hinz. }
    apply Hincl in HA; inversion HA; [left|right].
    * destruct a; simpl in H; simpl.
      rewrite <- (rew_opp_r id h2n_at i); rewrite H.
      now rewrite rew_opp_r.
    * clear - H.
      rewrite <- (rew_opp_r id h2n_at z).
      apply (in_map (fun x => rew [id] h2n_at in x)) in H.
      rewrite map_map in H.
      assert (map (fun x => rew [id] h2n_at in rew <- [id] h2n_at in fst x) L = map (fun z0  => fst z0) L).
      { apply map_ext; intros a; now rewrite rew_opp_r. }
      now rewrite H0 in H.
Qed.



Proposition h2n : forall A, hprove A ->
  forall L, Forall (fun z => closed z) (map snd L) ->
            incl (hffreevars A) (map (fun z => rew <- [id] h2n_at in fst z) L) ->
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
- remember (map (fun x => (rew [id] h2n_at in x, dvar 0)) (hffreevars A)) as LA.
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
            constructor; now rewrite rew_opp_l.
      -- assumption.
  + subst AAA; apply IHpi2.
    * rewrite map_app; apply Forall_app; [ assumption | subst LA ].
      remember (hffreevars A) as l; clear; induction l; simpl; now constructor.
    * rewrite map_app; apply incl_appr.
      subst LA; remember (hffreevars A) as l; clear; induction l; simpl.
      -- apply incl_refl.
      -- apply incl_cons; [ | now apply incl_tl ].
         constructor; now rewrite rew_opp_l.
- rewrite multi_subs_frl.
  rewrite h2n_fsubs.
  rewrite multi_subs_subs; try assumption.
  + destruct (in_dec vatomEq.eq_dec (rew [id] h2n_at in x) (ffreevars (h2n_formula A))) as [Hf|Hf].
    * apply frle.
      -- clear - f Hcl Hsub Hf.
         apply multi_tsubs_is_closed; [ assumption | ].
         intros a Hin.
         unfold incl in Hsub; specialize Hsub with (rew <- [id] h2n_at in a); simpl in Hsub.
         assert (In (rew <- [id] h2n_at in a) (hffreevars (hfsubs x t A))) as HvA.
         { rewrite h2n_ffreevars in Hf.
           apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hin.
           rewrite h2n_freevars in Hin.
           rewrite map_map in Hin.
           assert (map (fun x => rew <- [id] h2n_at in rew [id] h2n_at in x) (hfreevars t)
                 = map id (hfreevars t)) as Hmap
             by now apply map_ext; intros z; rewrite rew_opp_l.
           rewrite map_id in Hmap.
           rewrite Hmap in Hin; clear Hmap.
           apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hf.
           rewrite map_map in Hf.
           assert (map (fun x => rew <- [id] h2n_at in rew [id] h2n_at in x) (hffreevars A)
                 = map id (hffreevars A)) as Hmap
             by now apply map_ext; intros z; rewrite rew_opp_l.
           rewrite map_id in Hmap.
           rewrite Hmap in Hf; clear Hmap.
           rewrite rew_opp_l in Hf.
           now apply hffreevars_to_subs. }
         eapply or_intror in HvA; apply in_or_app in HvA; eapply Hsub in HvA.
         apply (in_map (fun x => rew [id] h2n_at in x)) in HvA.
         rewrite map_map in HvA.
         assert (map (fun x => rew [id] h2n_at in rew <- [id] h2n_at in fst x) L = map (fun z => fst z) L)
           as Hmap by now apply map_ext; intros z; rewrite rew_opp_r.
         rewrite Hmap in HvA.
         now rewrite <- (rew_opp_r id h2n_at a).
      -- apply ax_hd.
    * assert (~ In (rew [id] h2n_at in x)
                   (ffreevars (multi_subs (remove_snd (rew [id] h2n_at in x) L) (h2n_formula A)))) as Hnin.
      { intros Hin; apply Hf; apply multi_subs_ffreevars in Hin; try assumption.
        clear - Hcl; apply Forall_forall; intros a Hin.
        apply Forall_forall with (x:=a) in Hcl; [ assumption | ].
        revert Hin; clear; induction L; simpl; intros Hin.
        - inversion Hin.
        - destruct a0; simpl; simpl in Hin.
          case_eq (beq_vat (rew [id] h2n_at in x) i); intros Heq; rewrite Heq in Hin.
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
    apply Forall_forall with (x:=rew <- [id] h2n_at in z) in f.
    * revert f; clear; hformula_induction A.
      -- left; intros Heq; apply H1; subst.
         now rewrite rew_opp_l.
      -- right; intros Hin; apply H1.
         revert Hin; clear; hformula_induction A.
         ++ rewrite map_map in Hin.
            rewrite <- (rew_opp_l id h2n_at x).
            apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hin.
            rewrite h2n_remove in Hin.
            rewrite concat_map in Hin.
            rewrite map_map in Hin.
            assert (map (fun x => map (fun y => rew <- [id] h2n_at in y) (freevars (h2n_term x))) l
                  = map hfreevars l) as Heq.
            { apply map_ext; intros a.
              rewrite h2n_freevars, map_map.
              replace (hfreevars a) with (map id (hfreevars a)) at 2 by apply map_id.
              apply map_ext; intros b; now rewrite rew_opp_l. }
            now rewrite <- Heq.
         ++ rewrite remove_app in Hin; apply in_app_or in Hin.
            rewrite remove_app; apply in_or_app.
            now destruct Hin as [Hin|Hin]; [ left; apply A1 | right; apply IHA1 ].
         ++ clear IHA.
            rewrite h2n_ffreevars in Hin.
            rewrite <- (rew_opp_l id h2n_at x).
            apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hin.
            rewrite 2 h2n_remove in Hin.
            rewrite map_map in Hin.
            assert (map (fun x => rew <- [id] h2n_at in rew [id] h2n_at in x) (hffreevars A)
                  = map id (hffreevars A)) as Heq.
            { apply map_ext; intros a; now rewrite rew_opp_l. }
            rewrite map_id in Heq.
            now rewrite <- Heq.
    * revert Hinz; clear; hterm_induction t; intros Hin.
      -- destruct Hin; subst.
         ++ left; now rewrite rew_opp_l.
         ++ inversion H.
      -- revert IHl Hin; induction l; simpl; intros Hl Hin.
         ++ inversion Hin.
         ++ inversion Hl; subst.
            apply in_app_or in Hin.
            apply in_or_app.
            now destruct Hin as [Hin|Hin]; [left; apply H1 |right; apply IHl].
- rewrite ? multi_subs_frl.
  rewrite <- multi_subs_remove with (x:=rew [id] h2n_at in x) in HeqAA; try assumption.
  + apply frli; simpl.
    apply impe with (fupz AA); [ | apply ax_hd ].
    rewrite multi_subs_imp; simpl; rewrite <- HeqAA.
    replace (imp (fupz AA) (subs (rew [id] h2n_at in x) (dvar 0)
                                (fupz (multi_subs (remove_snd (rew [id] h2n_at in x) L) (h2n_formula B)))))
       with (imp (subs (rew [id] h2n_at in x) (dvar 0) (fupz AA))
                           (subs (rew [id] h2n_at in x) (dvar 0)
                                 (fupz (multi_subs (remove_snd (rew [id] h2n_at in x) L) (h2n_formula B))))).
    2:{ f_equal.
        enough (~ In (rew [id] h2n_at in x) (ffreevars (fupz AA))) as Hf by now apply nfree_subs.
        intros Hin; apply n; clear - Hcl HeqAA Hin.
        rewrite ffreevars_fup in Hin.
        apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hin.
        rewrite <- (rew_opp_l id h2n_at x).
        assert (map (fun x => rew <- [id] h2n_at in x) (map (fun x => rew [id] h2n_at in x) (hffreevars A))
              = map id (hffreevars A)) as Heq.
        { rewrite map_map; apply map_ext; intros a; now rewrite rew_opp_l. }
        rewrite map_id in Heq.
        rewrite <- Heq.
        rewrite <- h2n_ffreevars.
        subst; remember (h2n_formula A) as B; clear - Hcl Hin; rewrite rew_opp_l in Hin; rewrite rew_opp_l.
        revert B Hcl Hin; induction L; simpl; intros A Hcl Hin; [ assumption | ].
        destruct a; simpl in Hin, Hcl; inversion Hcl; subst.
        case_eq (beq_vat (rew [id] h2n_at in x) i); intros Heq; rewrite Heq in Hin.
        - now apply IHL.
        - simpl in Hin; apply IHL in Hin; [ | assumption ].
          apply (in_map (fun x => rew [id] h2n_at in x)) in Hin.
          rewrite map_map in Hin.
          assert (map (fun x : id vatom => rew [id] h2n_at in rew <- [id] h2n_at in x) (ffreevars (subs i t A))
                = map id (ffreevars (subs i t A))) as Hr.
          { apply map_ext; intros a; now rewrite rew_opp_r. }
          rewrite map_id in Hr.
          rewrite Hr in Hin.
          apply ffreevars_subs in Hin.
          destruct Hin as [Hin|Hin].
          + exfalso; rewrite H1 in Hin; inversion Hin.
          + apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hin.
            now rewrite rew_opp_l in Hin. }
    change (imp (subs (rew [id] h2n_at in x) (dvar 0) (fupz AA))
                (subs (rew [id] h2n_at in x) (dvar 0)
                      (fupz (multi_subs (remove_snd (rew [id] h2n_at in x) L) (h2n_formula B)))))
      with (subs (rew [id] h2n_at in x) (dvar 0) (imp (fupz AA)
                      (fupz (multi_subs (remove_snd (rew [id] h2n_at in x) L) (h2n_formula B))))).
    apply frle; [ reflexivity | ].
    change (fupz AA :: frl (rew [id] h2n_at in x)
              (imp (fupz AA) (fupz (multi_subs (remove_snd (rew [id] h2n_at in x) L) (h2n_formula B)))) :: nil)
      with ((fupz AA :: nil) ++ frl (rew [id] h2n_at in x)
              (imp (fupz AA) (fupz (multi_subs (remove_snd (rew [id] h2n_at in x) L) (h2n_formula B)))) :: nil).
    apply ax.
  + intros Hin; apply n; clear - Hin.
    rewrite h2n_ffreevars in Hin.
    rewrite <- (rew_opp_l id h2n_at x).
    apply (in_map (fun x => rew <- [id] h2n_at in x)) in Hin.
    rewrite map_map in Hin.
    assert (map (fun x => rew <- [id] h2n_at in rew [id] h2n_at in x) (hffreevars A) = map id (hffreevars A))
      as Heq.
    { apply map_ext; intros a; now rewrite rew_opp_l. }
    rewrite map_id in Heq.
    now rewrite <- Heq.
- rewrite multi_subs_frl.
  apply frli; simpl.
  rewrite fup_multi_subs.
  rewrite h2n_fup.
  replace (subs (rew [id] h2n_at in x) (dvar 0)
          (multi_subs (map (fun x0=> (fst x0, tup 0 (snd x0))) (remove_snd (rew [id] h2n_at in x) L))
             (h2n_formula A)))
     with (multi_subs ((map (fun x0 => (fst x0, tup 0 (snd x0))) (remove_snd (rew [id] h2n_at in x) L) ++
             (rew [id] h2n_at in x, dvar 0) :: nil)) (h2n_formula A))
    by now unfold multi_subs; rewrite fold_left_app; simpl.
  apply IHpi.
  + rewrite map_app; apply Forall_app.
    * rewrite map_map; simpl.
      revert Hcl; clear; induction L; simpl; intros HF; [ now constructor | ].
      inversion HF; subst.
      destruct a; simpl; simpl in H1.
      case_eq (beq_vat (rew [id] h2n_at in x) i); intros Heq; simpl.
      -- now apply IHL.
      -- constructor; [ | now apply IHL ].
         now rewrite freevars_tup.
    * now repeat constructor.
  + clear - Hsub; simpl in Hsub.
    intros a Hin.
    rewrite map_app; apply in_or_app.
    destruct (hatomEq.eq_dec x a); subst; [ right | left ]; simpl.
    * now left; rewrite rew_opp_l.
    * unfold incl in Hsub; specialize Hsub with a.
      apply notin_remove with hatomEq.eq_dec _ _ x in Hin; [ | intros Heq; now apply n ].
      apply Hsub in Hin.
      rewrite map_map; simpl.
      apply notin_remove with hatomEq.eq_dec _ _ x in Hin; [ | intros Heq; now apply n ].
      assert (map (fun z => rew <- [id] h2n_at in fst z) L
            = map (fun z => rew <- [id] h2n_at in z) (map fst L)) as Hmap
        by now rewrite map_map; apply map_ext; intros e.
      rewrite Hmap in Hin.
      rewrite <- h2n_remove in Hin.
      rewrite remove_snd_remove in Hin.
      now rewrite map_map in Hin.
Qed.

