(* Results missing in the standard library *)

Require Import Wf_nat Lia Peano_dec Eqdep_dec.
Require Vector.

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

Lemma Forall_incl {A} : forall P (l1 l2 : list A),
  incl l2 l1 -> Forall P l1 -> Forall P l2.
Proof.
intros Pl l1 l2 Hincl HF.
apply Forall_forall; intros a Ha.
apply Forall_forall with (x:=a) in HF; intuition.
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
Tactic Notation "specialize_Forall" hyp(H) "with" constr(x) := specialize_Forall H x.
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

Lemma incl_remove {A} : forall Hdec l (x : A), incl (remove Hdec x l) l.
Proof.
induction l; simpl; intros x y Hy; intuition.
destruct (Hdec x a); subst.
- apply IHl in Hy; intuition.
- destruct Hy as [Hy|Hy]; [left|right]; intuition.
  now apply IHl in Hy.
Qed.

Lemma notin_remove_eq {A} : forall Hdec l (x : A), ~ In x l ->
  remove Hdec x l = l.
Proof.
induction l; simpl; intuition.
destruct (Hdec x a); subst; intuition.
f_equal; intuition.
Qed.

Lemma remove_remove_eq {T} : forall Hdec l (x : T),
  remove Hdec x (remove Hdec x l) = remove Hdec x l.
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

Lemma remove_incl {A} : forall Hdec l1 l2 (x : A),
  incl l1 l2 -> incl (remove Hdec x l1) (remove Hdec x l2).
Proof.
intros Hdec l1 l2 x Hincl y Hin.
apply in_remove in Hin; destruct Hin as [Hin Hneq].
apply notin_remove; intuition.
Qed.

Lemma remove_concat {A} : forall Hdec (x : A) l,
  remove Hdec x (concat l) = flat_map (remove Hdec x) l.
Proof.
induction l; [ reflexivity | simpl ].
rewrite remove_app, IHl; reflexivity.
Qed.

Lemma incl_nil {A} : forall l : list A, incl nil l.
Proof. intros l a Hin; inversion Hin. Qed.

Lemma incl_nil_inv {T} : forall (l : list T), incl l nil -> l = nil.
Proof. now induction l; intros Hincl; [ | exfalso; apply Hincl with a; constructor ]. Qed.

Lemma incl_cons_inv {A} : forall (a:A) (l m:list A),
  incl (a :: l) m -> In a m /\ incl l m.
Proof.
intros a l m Hi.
split.
- apply Hi.
  constructor.
  reflexivity.
- intros b Hin.
  apply Hi.
  apply in_cons.
  assumption.
Qed.

Lemma incl_app_inv {A} : forall l m n : list A,
  incl (l ++ m) n -> incl l n /\ incl m n.
Proof.
induction l; intros m n Hin; split; auto.
- apply incl_nil.
- intros b Hb; inversion_clear Hb; subst; apply Hin.
  + now constructor.
  + simpl; apply in_cons.
   apply incl_appl with l; [ apply incl_refl | assumption ].
- apply IHl.
  now apply incl_cons_inv in Hin.
Qed.

Lemma concat_is_nil {T} : forall (L : list (list T)), concat L = nil <-> Forall (fun x => x = nil) L.
Proof.
induction L; simpl; split; intros Hc; try constructor.
- now apply app_eq_nil in Hc.
- apply IHL; now apply app_eq_nil in Hc.
- inversion Hc; subst; simpl.
  now apply IHL.
Qed.

Lemma in_concat {A} : forall (l : list A) (L : list (list A)) a, In a l -> In l L -> In a (concat L).
Proof.
  intros l L a Hin1 Hin2.
  induction L; simpl; inversion_clear Hin2; subst.
  - clear IHL; induction l; inversion_clear Hin1; [left|right]; intuition.
  - apply in_or_app; intuition.
Qed.

Lemma in_flat_map_Exists {A B} : forall (f : A -> list B) x l,
  In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
Proof. intros f x l; rewrite in_flat_map; split; apply Exists_exists. Qed.

Lemma notin_flat_map_Forall {A B} : forall (f : A -> list B) x l,
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

Lemma Vector_map_id {A n} : forall (v : Vector.t A n),
  Vector.map (fun x => x) v = v.
Proof. induction v; simpl; auto; rewrite IHv; auto. Qed.

Lemma Vector_map_map {A B C n} : forall (f:A->B) (g:B->C) (v : Vector.t A n),
  Vector.map g (Vector.map f v) = Vector.map (fun x => g (f x)) v.
Proof.
induction v; simpl; auto.
rewrite IHv; auto.
Qed.

Lemma Vector_map_ext_in {A B n} : forall (f g:A->B) (v : Vector.t A n),
  (forall a, Vector.In a v -> f a = g a) -> Vector.map f v = Vector.map g v.
Proof.
  induction v; simpl; auto.
  intros; rewrite H by constructor; rewrite IHv; intuition.
  apply H ; now constructor.
Qed.

Lemma Vector_map_ext {A B n} : forall (f g:A->B), (forall a, f a = g a) ->
  forall (v : Vector.t A n), Vector.map f v = Vector.map g v.
Proof. intros; apply Vector_map_ext_in; auto. Qed.

Lemma inj_pairT2_nat : forall (P:nat -> Type) p x y,
  existT P p x = existT P p y -> x = y.
Proof.
apply inj_pair2_eq_dec.
apply eq_nat_dec.
Qed.

Lemma Vector_Forall_forall {A} : forall P n (v : Vector.t A n),
  Vector.Forall P v <-> forall a, Vector.In a v -> P a.
Proof.
intros P n v ; split.
- intros HP a Hin.
  revert HP ; induction Hin ; intros HP ; inversion HP ; subst.
  + assumption.
  + apply inj_pairT2_nat in H1 ; subst ; auto.
- induction v ; intros Hin ; constructor.
  + apply Hin ; constructor.
  + apply IHv ; intros a Ha.
    apply Hin ; now constructor.
Qed.

Definition list_max l := fold_right max 0 l.

Lemma list_max_lt : forall l n, l <> nil ->
  list_max l < n <-> Forall (fun k => k < n) l.
Proof.
induction l; simpl; intros n Hnil; split; intros H; intuition; try lia.
- destruct l.
  + repeat constructor; lia.
  + constructor; [ | apply IHl ]; try lia.
    intros Heq; inversion Heq.
- destruct l; inversion_clear H.
  + simpl; lia.
  + apply IHl in H1; try lia.
    intros Heq; inversion Heq.
Qed.

Lemma NoDup_rev {A} : forall l : list A, NoDup l -> NoDup (rev l).
Proof.
induction l; simpl; intros Hnd; [ constructor | ].
inversion_clear Hnd as [ | ? ? Hnin Hndl ].
assert (Add a (rev l) (rev l ++ a :: nil)) as Hadd
  by (rewrite <- (app_nil_r (rev l)) at 1; apply Add_app).
apply NoDup_Add in Hadd; apply Hadd; intuition.
now apply Hnin, in_rev.
Qed.

Lemma seq_S : forall s l, seq s (S l) = seq s l ++ s + l :: nil.
Proof.
intros s l.
change (s + l :: nil) with (seq (s + l) 1).
rewrite <- seq_app.
f_equal; lia.
Qed.

Lemma NoDup_seq : forall s l, NoDup (seq s l).
Proof.
intros s l; revert s; induction l; simpl; intros s; constructor; intuition.
apply in_seq in H; lia.
Qed.

Lemma flat_map_map : forall (A B C:Type)(f:A->B)(g:B-> list C) l,
  flat_map g (map f l) = flat_map (fun x => g (f x)) l.
Proof. intros; rewrite flat_map_concat_map, map_map, <- flat_map_concat_map; reflexivity. Qed.

Lemma elt_eq_app {A} : forall l1 (a : A) l2 l3 l4,
  l1 ++ a :: l2 = l3 ++ l4 ->
    { l2' & l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 }
  + { l4' & l1 = l3 ++ l4' /\ l4' ++ a :: l2 = l4 }.
Proof.
induction l1; destruct l3; simpl; intros l4 Heq; inversion Heq; subst;
  try (now (left + right); eexists).
apply IHl1 in H1.
now destruct H1 as [ [? [? ?]] | [? [? ?]]]; subst; [left | right] ; eexists.
Qed.

