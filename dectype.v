(* Types with decidable equality formalized as types with Boolean valued equality *)
(*   as well as a study of infinite types *)

Require Import Bool PeanoNat Wf_nat Lia List.
Require Import stdlib_more.

Set Implicit Arguments.

(** * Decidable Types *)
(* types with a boolean binary predicate equivalent to equality *)

Record DecType := {
  car :> Type;
  eqb : car -> car -> bool;
  eqb_eq : forall x y, eqb x y = true <-> x = y
}.
Arguments eqb {_}.
Arguments eqb_eq {_}.

(* the [nat] instance *)
Definition nat_dectype := {|
  car := nat;
  eqb := Nat.eqb;
  eqb_eq := Nat.eqb_eq
|}.


Section DecTypes.

  Context { X : DecType }.
  Implicit Type x y : X.

  Lemma eqb_refl : forall x, eqb x x = true.
  Proof. intros x; apply (proj2 (eqb_eq x x) eq_refl). Qed.

  Lemma eqb_neq : forall x y, eqb x y = false <-> x <> y.
  Proof.
  intros x y; case_eq (eqb x y); intros Heq; split; intros; intuition.
  - apply eqb_eq in Heq; subst; intuition.
  - subst; rewrite eqb_refl in Heq; inversion Heq.
  Qed.

  Lemma eq_dt_dec : forall x y, { x = y } + { x <> y }.
  Proof.
  intros x y; case_eq (eqb x y); intros Heq; [ left | right ].
  - now apply eqb_eq in Heq.
  - now apply eqb_neq in Heq.
  Qed.

  Lemma eq_dt_reflect : forall x y, reflect (x = y) (eqb x y).
  Proof.
  intros x y; case_eq (eqb x y); intros Heq.
  - now apply ReflectT, eqb_eq.
  - now apply ReflectF, eqb_neq.
  Qed.

  Lemma if_eq_dt_dec_refl {A}: forall x (u v : A),
    (if eq_dt_dec x x then u else v) = u.
  Proof. intros x u v; now destruct (eq_dt_dec x x). Qed.

  Lemma if_eq_dt_dec_neq {A}: forall x y, x <> y -> forall (u v : A),
    (if eq_dt_dec x y then u else v) = v.
  Proof. intros x y Hneq u v; now destruct (eq_dt_dec x y). Qed.

  (* remove an element from a DecType *)
  Definition minus x : DecType.
  Proof.
  split with ({ z | eqb x z = false }) (fun a b => eqb (proj1_sig a) (proj1_sig b)).
  intros [x1 Hx1] [x2 Hx2]; simpl; split; intros Heq.
  - apply eqb_eq in Heq; subst.
    now rewrite ((Eqdep_dec.UIP_dec bool_dec) _ _ Hx1 Hx2).
  - inversion Heq; apply eqb_refl.
  Defined.

End DecTypes.

(* a tactic for automatic case analysis on equalities on a [DecType] *)
Ltac case_analysis :=
let Heq := fresh "Heq" in
let Heqeq := fresh "Heqeq" in
match goal with
| |- context f [?x =? ?y] => case_eq (x =? y); intros Heq
| |- context f [?x <? ?y] => case_eq (x <? y); intros Heq
| |- context f [?x ?= ?y] => case_eq (x ?= y); intros Heq
| |- context f [eqb ?x ?x] => rewrite (eqb_refl x)
| |- context f [eqb ?x ?y] => case eq_dt_reflect; intros Heq; [ try subst x | ]
| |- context f [eq_dt_dec ?x ?x] => rewrite (if_eq_dt_dec_refl x)
| H : ?x <> ?y |- context f [eq_dt_dec ?x ?y] => rewrite (if_eq_dt_dec_neq x y H)
| H : ?y <> ?x |- context f [eq_dt_dec ?x ?y] => rewrite (if_eq_dt_dec_neq x y (not_eq_sym H))
| |- context f [eq_dt_dec ?x ?y] => case_eq (eq_dt_dec x y); intros Heq Heqeq; [ subst x | ]
end; simpl.


(** * Infinite Types *)

(** ** Preliminary Definitions *)

(* a pigeonhole principle *)
Definition pigeon X := forall (l1 l2 : list X),
  NoDup l1 -> length l2 < length l1 -> { x | In x l1 & ~ In x l2 }.

(* injective functions *)
Notation injective f := (forall x y, f x = f y -> x = y).

Lemma comp_inj {A B C} : forall (f : B -> C) (g : A -> B),
  injective f -> injective g -> injective (fun x => f (g x)).
Proof. intuition. Qed.

Notation retract s i := (forall x, s (i x) = x).
Lemma section_inj {A B} : forall (i : A -> B) s, retract s i -> injective i.
Proof. intros i s Hsec x y Hf; rewrite <- Hsec, <- Hf; intuition. Qed.

Lemma inj_NoDup {A B} : forall f : A -> B, injective f ->
  forall l, NoDup l -> NoDup (map f l).
Proof.
intros f Hinj l; induction l; simpl; intros Hnd;
  inversion_clear Hnd as [ | ? ? Hnin Hnd2] ; constructor.
- intros Hin; apply Hnin.
  destruct (proj1 (in_map_iff _ _ _) Hin) as [x [Heq Hin2]].
  now apply Hinj in Heq; subst.
- now apply IHl.
Qed.

(* bijective functions *)
Notation bijective f := (forall y, { x | y = f x & forall x', y = f x' -> x = x' }).

Lemma id_bijective {A} : bijective (@id A).
Proof. intros x; exists x; unfold id; simpl; intuition. Qed.

Lemma bijective_inverse {A B} : forall f : A -> B, bijective f ->
  { g : B -> A | retract f g & retract g f }.
Proof.
intros f Hbij.
exists (fun x => proj1_sig (sig_of_sig2 (Hbij x))).
- intros x; simpl; destruct (Hbij x) as [y Heq _]; auto.
- intros x; simpl; destruct (Hbij (f x)) as [y _ Heq]; auto.
Qed.

Lemma bijective_injective {A B} : forall f : A -> B, bijective f -> injective f.
Proof.
intros f Hbij.
destruct (bijective_inverse _ Hbij) as [g _ Hsec].
now apply section_inj with g.
Qed.



(* The following results are proved in the case of a DecType:
     bijection with nat => section with nat => non-surjective self injection => injection from nat
     injection from nat <=> choice out of finite subsets
*)


(* we start with results true for arbitrary Type:
     bijection with nat => section with nat => choice out of finite subsets => injection from nat
     bijection with nat => non-surjective self injection
*)
Section Infinite.

Variable X : Type.

(* bijection with nat *)
Definition nat_biject := { f : nat -> X & bijective f }.
(* section with nat *)
Definition nat_section := {'(i,s) : (nat -> X) * (X -> nat) | retract s i }.
(* non-surjective self injection *)
Definition self_inject := { f : X -> X & injective f & { x | forall y, x <> f y } }.
(* injection from nat *)
Definition nat_inject := { f : nat -> X | injective f }.
(* choice out of finite subsets *)
Definition choice_out_finite := { f : list X -> X | forall l, ~ In (f l) l }.

Lemma nat_biject_section : nat_biject -> nat_section.
Proof.
intros [i Hbij].
destruct (bijective_inverse _ Hbij) as [s _ Hsec].
now exists (i, s).
Qed.

Lemma section_choice : nat_section -> choice_out_finite.
Proof.
intros [(i,s) Hsec].
remember (fix h l :=
  match l with
  | nil => i 0
  | x :: tl => i (S (max (s x) (s (h tl))))
  end) as c; exists c.
enough (forall l, Forall (fun x => s x < s (c l)) l) as Hlt.
{ intros l Hin; specialize Hlt with l.
  apply Forall_forall with (x:= c l) in Hlt; [ lia | assumption ]. }
induction l; simpl; intuition; constructor.
- rewrite Heqc, Hsec; lia.
- apply Forall_forall; intros b Hb; apply Forall_forall with (x:= b) in IHl; [ | assumption ].
  subst; rewrite Hsec; lia.
Qed.

Lemma choice_nat_inject : choice_out_finite -> nat_inject.
Proof.
intros [c Hc].
remember (fix h n := (* a non-empty list of iterated choices *)
  match n with
  | 0 => c nil :: nil
  | S k => c (h k) :: h k
  end) as ih.
exists (fun n => hd (c nil) (ih n)).
assert(forall n x, In (hd (c nil) (ih x)) (ih (n + x))) as HC.
{ induction n; simpl; intros x.
  - subst; destruct x; intuition.
  - subst; apply in_cons; intuition. }
enough (forall x y, x < y -> hd (c nil) (ih x) = hd (c nil) (ih y) -> x = y) as Hlt.
{ intros x y Heq.
  case (Nat.compare_spec x y); intros Ho; try lia.
  - now apply Hlt; [ lia | ].
  - symmetry; now apply Hlt; [ lia | ]. }
intros x y Hlt Heq; exfalso.
specialize HC with (y - S x) x.
replace (y - S x + x) with (pred y) in HC by lia.
rewrite Heq in HC.
replace y with (S (pred y)) in HC at 1 by lia.
now apply (Hc (ih (pred y))); subst.
Qed.

Lemma nat_biject_self : nat_biject -> self_inject.
Proof.
intros [i Hbij].
destruct (bijective_inverse _ Hbij) as [s Hsec1 Hsec2].
exists (fun x => i (S (s x))).
- apply comp_inj; [ | apply comp_inj ].
  + now apply section_inj with s.
  + intros x y; lia.
  + now apply section_inj with i.
- exists (i 0); intros x Heq.
  apply section_inj with _ _ 0 (S (s x)) in Hsec2; intuition.
  inversion Hsec2.
Qed.

End Infinite.


(* Implications requiring a DecType
     section with nat => non-surjective self injection => injection from nat
     injection from nat => choice out of finite subset
*)
Section InfiniteDec.

Context { X : DecType }.

Lemma section_self_inject : nat_section X -> self_inject X.
Proof.
intros [(i, s) Hs].
assert (Hinj := section_inj _ _ Hs).
assert (forall x z, x = i z -> x = i (s x)) as Hsi
  by (now intros x z Heq; rewrite Heq at 2; rewrite Hs); clear Hs.
exists (fun x => if eqb x (i (s x)) then i (S (s x)) else x).
- intros x y.
  repeat case_analysis; intros Heqh; intuition.
  + rewrite Heq, Heq0; f_equal.
    apply Hinj in Heqh.
    now inversion Heqh.
  + exfalso; apply Heq0.
    symmetry in Heqh.
    eapply Hsi; eassumption.
  + exfalso; apply Heq.
    eapply Hsi; eassumption.
- exists (i 0); intros x.
  case_analysis; intros Heqi.
  + apply Hinj in Heqi; inversion Heqi.
  + apply Heq.
    symmetry in Heqi.
    eapply Hsi; eassumption.
Qed.

Lemma pigeon_dectype : pigeon X.
Proof.
intros l1; induction l1; simpl; intros l2 Hnd Hl; [ exfalso; lia | ].
destruct (in_dec eq_dt_dec a l2).
- apply NoDup_NoDup_Type in Hnd.
  inversion_clear Hnd as [ | ? ? Hnin Hnd2 ].
  apply NoDup_Type_NoDup in Hnd2.
  apply notin_Type_notin in Hnin.
  apply IHl1 with (remove eq_dt_dec a l2) in Hnd2.
  + destruct Hnd2 as [b Hb Hnb].
    exists b.
    * now apply in_cons.
    * intros Hin; apply Hnb.
      apply notin_remove; [ | assumption ].
      intros Heq; subst; intuition.
  + apply remove_length with (Hdec:= eq_dt_dec) in i; lia.
- exists a; intuition.
Qed.

Lemma injective_enum : forall (f : nat -> X), injective f ->
  forall l, { n | ~ In (f n) l }.
Proof.
intros f Hinj l.
destruct pigeon_dectype with (map f (seq 0 (S (length l)))) l as [x Hin Hnin].
- now apply inj_NoDup, seq_NoDup.
- rewrite map_length, seq_length; lia.
- remember (S (length l)) as k; clear Heqk.
  remember 0 as s; clear Heqs.
  revert s Hin Hnin; induction k; simpl; intros s Hin Hnin; [ easy | ].
  case (eq_dt_reflect (f s) x); intros Heq; subst.
  + now exists s.
  + apply IHk with (S s); [ | assumption ].
    now destruct Hin.
Qed.

Lemma nat_inject_choice : nat_inject X -> choice_out_finite X.
Proof.
intros [i Hi].
exists (fun l => i (proj1_sig (injective_enum i Hi l))).
intros l Hin; destruct (injective_enum i Hi l) ; intuition.
Qed.

Lemma self_inject_minus : forall (pi : self_inject X),
  self_inject (minus (proj1_sig (projT3 pi))).
Proof.
intros [f Hinj [i Hi]]; simpl.
assert (forall x, eqb i x = false -> eqb i (f x) = false) as Hif
  by (intros x _; now apply eqb_neq).
split with (fun a => exist _ (f (proj1_sig a)) (Hif (proj1_sig a) (proj2_sig a))).
- intros [x Hx] [y Hy] Heq.
  inversion Heq as [ Heq2 ].
  apply Hinj in Heq2; subst.
  now rewrite ((Eqdep_dec.UIP_dec bool_dec) _ _ Hx Hy).
- assert (eqb i (f i) = false) as Hj by now apply eqb_neq.
  split with (exist _ (f i) Hj).
  intros [y Hy]; simpl; intros Heq.
  inversion Heq as [Heq2].
  now apply Hinj, eqb_neq in Heq2.
Qed.

End InfiniteDec.

Definition nat_of_self (X : DecType) (pi : self_inject X) (n : nat) :
   { x : X | x = Nat.iter n (projT1 (sigT_of_sigT2 pi)) (proj1_sig (projT3 pi)) }
 * { Y : DecType & self_inject Y }.
Proof.
remember pi as HX; destruct pi as [f Hinj [i Hi]].
induction n.
- split.
  + exists i; simpl; now subst.
  + exists (minus (proj1_sig (projT3 HX))).
    apply (self_inject_minus HX).
- destruct IHn as [y Y]; split.
  + destruct y as [y Hy].
    exists (f y); simpl; now subst.
  + destruct Y as [Y HY].
    exists (minus (proj1_sig (projT3 HY))).
    apply (self_inject_minus HY).
Defined.

Lemma self_inject_nat (X : DecType) : self_inject X -> nat_inject X.
Proof.
intros HX.
exists (fun n => proj1_sig (fst (nat_of_self X HX n))).
intros x y Heq.
destruct (fst (nat_of_self X HX x)) as [n Hn]; subst.
destruct (fst (nat_of_self X HX y)) as [m Hm]; subst; simpl in Heq.
destruct HX as [f Hinj [i Hi]]; simpl in Heq.
revert x y Heq.
enough (forall x y, x < y -> Nat.iter x f i = Nat.iter y f i -> x = y) as Hlt.
{ intros x y Heq.
  case (Nat.compare_spec x y); intros Ho; try lia.
  - now apply Hlt; [ lia | ].
  - symmetry; now apply Hlt; [ lia | ]. }
intros x y Hlt Heq; exfalso.
remember (pred (y - x)) as n.
replace y with (S n + x) in Heq by lia; clear Heqn.
revert Heq; induction x; simpl; intros Heq.
- now apply Hi in Heq.
- replace (S n + x) with (n + S x) in IHx by lia.
  now apply IHx, Hinj; [ lia | ].
Qed.


(** * Infinite Decidable Types *)
(* (infinite) decidable types with freshness function *)

Record InfDecType := {
  infcar :> DecType;
  fresh : list infcar -> infcar;
  fresh_prop : forall l, ~ In (fresh l) l
}.
Arguments fresh {_}.
Arguments fresh_prop {_}.

(* [nat] instance of [InfDecType] *)
Definition nat_infdectype := {|
  infcar := nat_dectype;
  fresh := (proj1_sig (section_choice (nat_biject_section (existT _ id (id_bijective)))));
  fresh_prop := (proj2_sig (section_choice (nat_biject_section (existT _ id (id_bijective)))));
|}.
(* alternative direct construction *)
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
(*
Definition nat_infdectype := {|
  infcar := nat_dectype;
  fresh := nat_fresh;
  fresh_prop := nat_fresh_prop
|}.
*)


Section InfDecTypes.

Context { X : InfDecType }.

Lemma infinite_nat_inject : nat_inject X.
Proof.
apply choice_nat_inject.
exists fresh.
apply fresh_prop.
Qed.

(* A list (of length [n]+1) of distinct fresh elements (not in [l]) *)
Fixpoint freshlist_of_list (l : list X)  n :=
  match n with
  | 0 => fresh l :: nil
  | S k => let lv := freshlist_of_list l k in fresh (lv ++ l) :: lv
  end.

Definition freshlist l n := hd (fresh l) (freshlist_of_list l n).

Lemma freshlist_of_list_fresh : forall l n x,
  In x (freshlist_of_list l n) -> ~ In x l.
Proof.
induction n; simpl; intros x Hin Hinl.
- destruct Hin; intuition.
  revert Hinl; subst; apply fresh_prop.
- destruct Hin; subst.
  + apply fresh_prop with (l0 := freshlist_of_list l n ++ l).
    apply in_or_app; intuition.
  + now apply IHn in Hinl.
Qed.

Lemma freshlist_of_list_prefix : forall l n m, n < m -> exists l',
  l' <> nil /\ freshlist_of_list l m = l' ++ freshlist_of_list l n.
Proof. induction m; intros Hlt; [ lia | ].
destruct (Nat.eq_dec n m); subst.
- now exists (fresh (freshlist_of_list l m ++ l) :: nil).
- assert (n < m) as Hlt2 by lia.
  apply IHm in Hlt2.
  destruct Hlt2 as [ l' [_ Heq] ].
  exists (fresh (freshlist_of_list l m ++ l) :: l'); split ;
    [ | now rewrite <- app_comm_cons, <- Heq ].
  intros Hnil; inversion Hnil.
Qed.

Lemma freshlist_of_list_NoDup : forall l n, NoDup (freshlist_of_list l n).
Proof. induction n; simpl; constructor; intuition.
- constructor.
- apply fresh_prop with (l0 := freshlist_of_list l n ++ l).
  apply in_or_app; intuition.
Qed.

Lemma freshlist_fresh : forall l n, ~ In (freshlist l n) l.
Proof.
intros l n Hin.
assert (In (freshlist l n) (freshlist_of_list l n)) as Hin2
  by (destruct n; left; reflexivity).
now apply freshlist_of_list_fresh in Hin2.
Qed.

Lemma freshlist_inj : forall l n m, freshlist l n = freshlist l m -> n = m.
Proof.
intros l.
enough (forall n m, n < m -> freshlist l n = freshlist l m -> n = m) as Hlt.
{ intros x y Heq.
  case (Nat.compare_spec x y); intros Ho; try lia.
  - now apply Hlt; [ lia | ].
  - symmetry; now apply Hlt; [ lia | ]. }
intros n m Hlt Heq; exfalso.
apply freshlist_of_list_prefix with (l:= l) in Hlt; destruct Hlt as [ l' [Hnil Hprf] ].
unfold freshlist in Heq; rewrite Hprf in Heq.
destruct l'; [ now apply Hnil | ]; simpl in Heq.
destruct n; simpl in Heq, Hprf; rewrite Heq in Hprf.
- assert (In c ((c :: l') ++ nil)) as Hin by intuition.
  revert Hin; apply NoDup_remove_2; rewrite <- app_comm_cons, <- Hprf.
  apply (freshlist_of_list_NoDup l m).
- assert (In c ((c :: l') ++ freshlist_of_list l n)) as Hin by intuition.
  revert Hin; apply NoDup_remove_2; rewrite <- app_comm_cons, <- Hprf.
  apply (freshlist_of_list_NoDup l m).
Qed.

End InfDecTypes.

