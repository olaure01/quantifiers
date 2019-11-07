(* Atoms for building terms and formulas *)

Require Import Bool PeanoNat Wf_nat Lia List.

Require Import stdlib_more.


Set Implicit Arguments.



Create HintDb term_db.

Tactic Notation "rnow" tactic(t) :=
  t ; simpl ; autorewrite with term_db in * ; simpl ; intuition.
Tactic Notation "rnow" tactic(t) "then" tactic(t1) :=
  t ; simpl ; autorewrite with term_db in * ; simpl ; intuition t1 ; simpl ; intuition.


(* TODO see if required and where to put *)
Lemma ltb_S : forall n m, (S n <? S m) = (n <? m).
Proof. reflexivity. Qed.
Hint Rewrite ltb_S : term_db.



(* Atom sets *)

Record Atom := {
  car :> Type;
  eqb_at : car -> car -> bool;
  eqb_eq : forall x y, eqb_at x y = true <-> x = y
}.
Arguments eqb_at {_}.
Arguments eqb_eq {_}.

Definition nat_atom := {|
  car := nat;
  eqb_at := Nat.eqb;
  eqb_eq := Nat.eqb_eq
|}.


Section Atoms.

  Context { atom : Atom }.

  Lemma eqb_refl : forall x : atom, eqb_at x x = true.
  Proof. intros x; apply (proj2 (eqb_eq x x) eq_refl). Qed.

  Lemma eqb_neq : forall x y : atom, eqb_at x y = false <-> x <> y.
  Proof.
  intros x y; split; intros H.
  - intros Heq; subst.
    rewrite eqb_refl in H.
    inversion H.
  - case_eq (eqb_at x y); intro Heq.
    + apply eqb_eq in Heq; subst.
      exfalso; apply H; reflexivity.
    + reflexivity.
  Qed.

  Lemma eq_at_dec : forall x y : atom, { x = y } + { x <> y }.
  Proof.
  intros x y.
  case_eq (eqb_at x y); intros Heq.
  - apply eqb_eq in Heq.
    left; assumption.
  - apply eqb_neq in Heq.
    right; assumption.
  Qed.

  Lemma if_eq_at_dec_refl {A:Type}: forall (x : atom) (u v : A),
    (if eq_at_dec x x then u else v) = u.
  Proof. intros x u v; destruct (eq_at_dec x x); easy. Qed.

  Lemma if_eq_at_dec_neq {A:Type}: forall (x y: atom), x <> y ->
    forall (u v : A), (if eq_at_dec x y then u else v) = v.
  Proof. intros x y Hneq u v; destruct (eq_at_dec x y); easy. Qed.

  Lemma eq_at_reflect : forall x y : atom, reflect (x = y) (eqb_at x y).
  Proof.
  intros x y; case_eq (eqb_at x y); intros Heq.
  - apply ReflectT.
    apply eqb_eq; assumption.
  - apply ReflectF.
    apply eqb_neq; assumption.
  Qed.

End Atoms.

Ltac case_analysis :=
let Heq := fresh "Heq" in
let Heqeq := fresh "Heqeq" in
match goal with
| |- context f [?x =? ?y] => case_eq (x =? y); intros Heq
| |- context f [?x <? ?y] => case_eq (x <? y); intros Heq
| |- context f [?x ?= ?y] => case_eq (x ?= y); intros Heq
| |- context f [eqb_at ?x ?x] => rewrite (eqb_refl x)
| |- context f [eqb_at ?x ?y] => case eq_at_reflect; intros Heq; [ try subst x | ]
| |- context f [eq_at_dec ?x ?x] => rewrite (if_eq_at_dec_refl x)
| H : ?x <> ?y |- context f [eq_at_dec ?x ?y] => rewrite (if_eq_at_dec_neq x y H)
| H : ?y <> ?x |- context f [eq_at_dec ?x ?y] => rewrite (if_eq_at_dec_neq x y (not_eq_sym H))
| |- context f [eq_at_dec ?x ?y] => case_eq (eq_at_dec x y); intros Heq Heqeq; [ subst x | ]
end; simpl.
Ltac rcauto := simpl ; autorewrite with term_db in * ; simpl ; rnow (repeat case_analysis).




(* Infinite sets *)

Definition pigeon X := forall (l1 l2 : list X),
  NoDup l1 -> length l2 < length l1 -> { x : _ & In x l1 & In x l2 -> False }.

Notation injective f := (forall x y, f x = f y -> x = y).
Lemma comp_inj {A B C} : forall (f : B -> C) (g : A -> B),
  injective f -> injective g -> injective (fun x => f (g x)).
Proof. intuition. Qed.

Lemma section_inj {A B} : forall (i : A -> B) s,
  (forall x, s (i x) = x) -> injective i.
Proof. intros i s Hsec x y Hf; rewrite <- Hsec, <- Hf; intuition. Qed.

Lemma inj_NoDup {A B} : forall f : A -> B, injective f ->
  forall l, NoDup l -> NoDup (map f l).
Proof.
induction l; simpl; intros Hnd.
- constructor.
- inversion Hnd; constructor; subst.
  + intros Hin; apply H2.
    apply in_map_iff in Hin.
    destruct Hin as [x [Heq Hin]].
    now apply H in Heq; subst.
  + now apply IHl.
Qed.

Notation bijective f := (forall y, { x | y = f x & forall x', y = f x' -> x = x' }).

Lemma bijective_injective {A B} : forall f : A -> B, bijective f -> injective f.
Proof.
intros f Hb x y Heq.
destruct (Hb (f x)) as [z Heqz Hz].
apply Hz in Heq.
assert (Heqx := eq_refl (f x)).
apply Hz in Heqx.
now subst.
Qed.



(* Results proved in the case of a decidable equality:
     bijection with nat => section with nat => non-surjective self injection => injection from nat
     injection from nat <=> choice out of finite subset
*)


(* Results true for arbitrary Type:
     bijection with nat => section with nat => choice out of finite subset => injection from nat
     bijection with nat => non-surjective self injection
*)
Section Infinite.

Variable X : Type.

Definition nat_biject := { f : nat -> X & bijective f }.
Definition self_inject := { f : X -> X & injective f & { x | forall y, x <> f y } }.
Definition section_from_nat := {'(i,s) : (nat -> X) * (X -> nat) & forall x, s (i x) = x }.
Definition choice_out_finite := { f : list X -> X | forall l, ~ In (f l) l }.
Definition nat_inject := { f : nat -> X | injective f }.



Lemma nat_biject_section : nat_biject -> section_from_nat.
Proof.
intros [i Hi].
remember (fun x => proj1_sig (sig_of_sig2 (Hi x))) as s.
exists (i,s).
intros x.
rewrite Heqs.
destruct (Hi (i x)); simpl.
now apply (bijective_injective _ Hi x0 x).
Qed.

Lemma section_choice : section_from_nat -> choice_out_finite.
Proof.
intros [(i,s) Hs].
remember (fix h l :=
  match l with
  | nil => i 0
  | x :: tl => i (S (max (s x) (s (h tl))))
  end) as c.
exists c.
enough (forall l, Forall (fun x => s x < s (c l)) l) as Hlt.
{ intros l Hin; specialize Hlt with l.
  apply Forall_forall with (x:=c l) in Hlt; [ lia | assumption ]. }
induction l; simpl; intuition; constructor.
- rewrite Heqc, Hs; lia.
- apply Forall_forall; intros b Hb; apply Forall_forall with (x:=b) in IHl; [ | assumption ].
  subst; rewrite Hs; lia.
Qed.

Lemma choice_nat_inject : choice_out_finite -> nat_inject.
Proof.
intros [c Hc].
remember (fix h n :=
  match n with
  | 0 => c nil :: nil
  | S k => c (h k) :: h k
  end) as ih.
exists (fun n => hd (c nil) (ih n)).
assert(forall n x, In (hd (c nil) (ih x)) (ih (n + x))) as HC.
{ induction n; simpl; intros x.
  - subst; destruct x; intuition.
  - subst; apply in_cons; intuition. }
intros x y Heq.
destruct (Compare_dec.lt_eq_lt_dec x y) as [C | C]; [ destruct C as [C | C] | ].
- exfalso.
  specialize HC with (y - S x) x.
  replace (y - S x + x) with (pred y) in HC by lia.
  rewrite Heq in HC.
  replace y with (S (pred y)) in HC at 1 by lia.
  now apply (Hc (ih (pred y))); subst.
- assumption.
- exfalso.
  specialize HC with (x - S y) y.
  replace (x - S y + y) with (pred x) in HC by lia.
  rewrite <- Heq in HC.
  replace x with (S (pred x)) in HC at 1 by lia.
  now apply (Hc (ih (pred x))); subst.
Qed.

Lemma nat_biject_self : nat_biject -> self_inject.
Proof.
intros [i Hi].
remember (fun x => proj1_sig (sig_of_sig2 (Hi x))) as s.
remember (fun x => i (S (s x))) as j.
exists j.
- intros x y Heq; subst j.
  assert (injective s) as Hinjs.
  { clear - Heqs; intros x y Heq; subst.
    assert (Hx := Hi x).
    destruct Hx.
    assert (Hy := Hi y).
    destruct Hy; subst.
    assert (forall z, proj1_sig (sig_of_sig2 (Hi (i z))) = z).
    { clear - Hi; intros z; simpl.
      destruct (Hi (i z)).
      now apply e0. }
      now rewrite 2 H in Heq; subst. }
  apply comp_inj in Heq; auto.
  now apply bijective_injective.
- exists (i 0); intros x Heq.
  clear Heqs; apply bijective_injective with _ 0 (S (s x)) in Hi.
  * inversion Hi.
  * now subst j.
Qed.

End Infinite.


(* Implications requiring decidable equality
     section with nat => non-surjective self injection => injection from nat
     injection from nat => choice out of finite subset
*)
Section InfiniteDec.

Context { X : Atom }.

Lemma section_self_inject : section_from_nat X -> self_inject X.
Proof.
intros [(i,s) Hs].
assert (Hinj := section_inj _ _ Hs).
exists (fun x => if eqb_at x (i (s x)) then i (S (s x)) else x).
intros x y.
repeat case_analysis; intros Heqh.
- apply Hinj in Heqh.
  inversion Heqh.
  rewrite Heq, Heq0.
  now f_equal.
- exfalso.
  apply Heq0.
  rewrite <- Heqh at 2.
  now rewrite Hs, Heqh.
- exfalso.
  apply Heq.
  rewrite Heqh at 2.
  now rewrite Hs, <- Heqh.
- assumption.
- exists (i 0); intros y.
  case_analysis; intros Heqi.
  + apply Hinj in Heqi; inversion Heqi.
  + apply Heq.
  rewrite <- Heqi at 2.
  now rewrite Hs, Heqi.
Qed.

Lemma pigeon_atom : pigeon X.
Proof.
intros l1.
remember (length l1) as n; revert l1 Heqn; induction n ; simpl; intros l1 Heqn l2 Hi Hl;
  try (exfalso; lia).
destruct l1; inversion Heqn; subst.
destruct (in_dec eq_at_dec c l2).
- specialize IHn with l1 (remove eq_at_dec c l2).
  apply NoDup_NoDup_Type in Hi.
  inversion Hi; subst.
  apply NoDup_Type_NoDup in X0.
  apply notin_Type_notin in H0.
  apply IHn in X0.
  + destruct X0 as [b Hb Hnb].
    assert (b <> c) as Hbc by (intros Heq; subst; intuition).
    exists b.
    * now apply in_cons.
    * intros Hin; apply Hnb.
      now apply notin_remove.
  + reflexivity.
  + apply remove_length with (Hdec:=eq_at_dec) in i.
    clear - i Hl; lia.
- exists c; intuition.
Qed.

Lemma injective_enum : forall (f : nat -> X), injective f ->
  forall l, { n & In (f n) l -> False }.
Proof.
intros f Hinj l.
remember (map f (seq 0 (S (length l)))) as ln.
destruct pigeon_atom with ln l as [x Hin Hnin].
- subst; apply inj_NoDup; [ assumption | ].
  apply seq_NoDup.
- subst; rewrite map_length, seq_length; lia.
- subst.
  remember (S (length l)) as k; clear Heqk.
  remember 0 as s; clear Heqs.
  revert s Hin Hnin; induction k; simpl; intros s Hin Hnin; [ easy | ].
  case (eq_at_reflect (f s) x); intros Heq; subst.
  + now exists s.
  + assert (In x (map f (seq (S s) k))) as Hin2
      by (destruct Hin; [ exfalso; auto |apply H ]).
    apply IHk in Hin2; auto.
Qed.

Lemma nat_inject_choice : nat_inject X -> choice_out_finite X.
Proof.
intros [i Hi].
exists (fun l => i (projT1 (injective_enum i Hi l))).
intros l Hin.
destruct (injective_enum i Hi l) ; intuition.
Qed.


Definition minus (e : X) : Atom.
Proof.
split with ({ x : X | eqb_at e x = false }) (fun a b => eqb_at (proj1_sig a) (proj1_sig b)).
intros [x Hx] [y Hy]; simpl; split; intros H.
- apply eqb_eq in H; subst.
  now rewrite ((Eqdep_dec.UIP_dec bool_dec) _ _ Hx Hy).
- inversion H; apply eqb_refl.
Defined.

Lemma self_inject_minus : forall (pi : self_inject X),
  self_inject { x : X | eqb_at (proj1_sig (projT3 pi)) x = false }.
Proof.
intros  [f Hinj [i Hi]]; simpl.
assert (forall x, eqb_at i x = false -> eqb_at i (f x) = false) as Hif
  by (intros x _; now apply eqb_neq).
split with (fun a => exist _ (f (proj1_sig a)) (Hif (proj1_sig a) (proj2_sig a))).
- intros [x Hx] [y Hy] Heq.
  inversion Heq.
  apply Hinj in H0; subst.
  now rewrite ((Eqdep_dec.UIP_dec bool_dec) _ _ Hx Hy).
- assert (eqb_at i (f i) = false) as Hj by now apply eqb_neq.
  split with (exist _ (f i) Hj).
  intros [y Hy]; simpl; intros Heq.
  inversion Heq as [Heq2].
  apply Hinj in Heq2.
  apply eqb_neq in Heq2; auto.
Qed.

End InfiniteDec.

Definition nat_of_self (X : Atom) (pi : self_inject X) (n : nat) :
  { x : X | x = Nat.iter n (projT1 (sigT_of_sigT2 pi)) (proj1_sig (projT3 pi)) } * { Y : Atom & self_inject Y }.
Proof.
remember pi as HX.
destruct pi as [f Hinj [i Hi]].
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

Lemma self_inject_nat (X : Atom) : self_inject X -> nat_inject X.
Proof.
intros HX.
exists (fun n => proj1_sig (fst (nat_of_self X HX n))).
intros x y Heq.
destruct (fst (nat_of_self X HX x)) as [n Hn]; subst.
destruct (fst (nat_of_self X HX y)) as [m Hm]; subst; simpl in Heq.
destruct HX as [f Hinj [i Hi]]; simpl in Heq.
destruct (Compare_dec.lt_eq_lt_dec x y) as [C | C]; [ destruct C as [C | C] | ].
- exfalso.
  remember (pred (y - x)) as n.
  replace y with (S n + x) in Heq by lia.
  revert Heq; clear C Heqn; induction x; simpl; intros Heq.
  + now apply Hi in Heq.
  + apply IHx.
    apply Hinj.
    now replace (S n + x) with (n + S x) by lia.
- assumption.
- exfalso.
  remember (pred (x - y)) as n.
  replace x with (S n + y) in Heq by lia.
  revert Heq; clear C Heqn; induction y; simpl; intros Heq.
  + symmetry in Heq; now apply Hi in Heq.
  + apply IHy.
    apply Hinj.
    now replace (S n + y) with (n + S y) by lia.
Qed.


(* (infinite) Atom sets with freshness function *)

Record InfAtom := {
  infcar :> Atom;
  fresh : list infcar -> infcar;
  fresh_prop : forall l, ~ In (fresh l) l
}.
Arguments fresh {_}.
Arguments fresh_prop {_}.

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
Definition infatom_nat := {|
  infcar := nat_atom;
  fresh := nat_fresh;
  fresh_prop := nat_fresh_prop
|}.

Section InfiniteAtom.

Context { atom : InfAtom }.

Lemma infinite_nat_inject : nat_inject atom.
Proof.
apply choice_nat_inject.
exists fresh.
apply fresh_prop.
Qed.

End InfiniteAtom.

