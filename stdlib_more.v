(* Results missing in the standard library *)

Require Import Wf_nat Lia.

Lemma lt_wf_rect :
  forall n (P:nat -> Type), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
intros n P Hw.
apply well_founded_induction_type with lt.
- apply lt_wf.
- assumption.
Qed.

Lemma lt_wf_double_rect :
 forall P:nat -> nat -> Type,
   (forall n m,
     (forall p q, p < n -> P p q) ->
     (forall p, p < m -> P n p) -> P n m) -> forall n m, P n m.
Proof.
  intros P Hrec p; pattern p; apply lt_wf_rect.
  intros n H q; pattern q; apply lt_wf_rect; auto with arith.
Defined.



Require Import List.

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

Ltac specialize_Forall H a := apply Forall_forall with (x:=a) in H; [ | assumption ].
Tactic Notation "specialize_Forall" hyp(H) "with" hyp(x) := specialize_Forall H x.
Ltac specialize_Forall_all a := repeat
match goal with
| H : Forall ?P ?l |- _ => specialize_Forall H with a
end.

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

Lemma notin_remove_eq {A} : forall Hdec l (x : A), ~ In x l ->
  remove Hdec x l = l.
Proof.
induction l; simpl; intuition.
destruct (Hdec x a); subst; intuition.
f_equal; intuition.
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

Lemma remove_concat {A} : forall Hdec (x : A) l,
  remove Hdec x (concat l) = flat_map (remove Hdec x) l.
Proof.
induction l; [ reflexivity | simpl ].
rewrite remove_app, IHl; reflexivity.
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

Lemma in_flat_map_Exists {A B : Type} : forall (f : A -> list B) x l,
  In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
Proof. intros f x l; rewrite in_flat_map; split; apply Exists_exists. Qed.

Lemma notin_flat_map_Forall {A B : Type} : forall (f : A -> list B) x l,
  ~ In x (flat_map f l) <-> Forall (fun y => ~ In x (f y)) l.
Proof. intros f x l; rewrite Forall_Exists_neg; apply not_iff_compat, in_flat_map_Exists. Qed.


Fixpoint In_Type {A} (a:A) (l:list A) : Type :=
    match l with
      | nil => False
      | b :: m => sum (b = a) (In_Type a m)
    end.

  Lemma in_Type_in {A} : forall (a : A) l, In_Type a l -> In a l.
  Proof.
  induction l; intros Hin; inversion Hin; try now constructor.
  right; intuition.
  Qed.

  Lemma notin_Type_notin {A} : forall (a : A) l, (In_Type a l -> False) -> ~ In a l.
  Proof.
  induction l; intros Hnin Hin; inversion Hin; subst.
  - apply Hnin; constructor; reflexivity.
  - apply IHl; [ | assumption ].
    intros Hin2; apply Hnin.
    right; assumption.
  Qed.

  Inductive NoDup_Type {A} : list A -> Type :=
    | NoDup_Type_nil : NoDup_Type nil
    | NoDup_Type_cons : forall x l, (In_Type x l -> False) -> NoDup_Type l -> NoDup_Type (x::l).

  Lemma NoDup_NoDup_Type {A} : forall l : list A, NoDup l -> NoDup_Type l.
  Proof.
  induction l; intros Hnd; constructor.
  - intros Hnin.
    apply in_Type_in in Hnin.
    inversion Hnd; intuition.
  - apply IHl; now inversion Hnd.
  Qed.

  Lemma NoDup_Type_NoDup {A} : forall l : list A, NoDup_Type l -> NoDup l.
  Proof.
  induction l; intros Hnd; constructor.
  - apply notin_Type_notin; intros Hnin.
    inversion Hnd; intuition.
  - apply IHl; now inversion Hnd.
  Qed.


Lemma remove_length {A} : forall Hdec l (x : A), In x l ->
  length (remove Hdec x l) < length l.
Proof.
induction l; simpl; intros x Hin.
- inversion Hin.
- destruct (Hdec x a) as [Heq | Hneq]; subst; simpl.
  + destruct (in_dec Hdec a l); intuition.
    rewrite notin_remove_eq; intuition.
  + destruct Hin as [Hin | Hin].
    * exfalso; now apply Hneq.
    * apply IHl in Hin; lia.
Qed.

