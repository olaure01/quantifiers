(* Definitions and properties of first-order terms *)
(*   with holes in [nat] for de Bruijn indices *)

Require Export PeanoNat.
Require Export List.

Require Import stdlib_more.

Require Export atom.

Set Implicit Arguments.



(** * First-Order Terms *)

Section Terms.

Context { vatom : Atom } { tatom : Type }.

(** terms with quantifiable variables *)
(** arity not given meaning that we have a copy of each function name for each arity *)
(** [dvar] for De Bruijn style eigen variables in proofs *)
(** [tvar] for quantified variables in formulas *)
Inductive term :=
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
      | cons t1 l1 => Forall_cons _
                        (term_ind_list_Forall t1 Pdvar Ptvar Pconstr)
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
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  apply (term_ind_list_Forall t) ;
  [ intros nn ; try reflexivity ; try assumption ; simpl
  | intros xx ; try reflexivity ; try assumption ; simpl
  | intros cc ll IHll ; simpl ;
    repeat (rewrite flat_map_concat_map) ; repeat (rewrite map_map) ;
    try f_equal ;
    try (apply map_ext_in ; intros i Hi; specialize_Forall_all i) ;
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i) ;
    try assumption ] ;
  try ((rnow idtac) ; fail) ; try (rcauto ; fail).


(** lift indexes above [k] in [term] [t] *)
Fixpoint tup k t :=
match t with
| dvar n => if n <? k then dvar n else dvar (S n)
| tvar x => tvar x
| tconstr f l => tconstr f (map (tup k) l)
end.

Lemma tup_tup_com : forall k t, tup (S k) (tup 0 t) = tup 0 (tup k t).
Proof. term_induction t. Qed.
Hint Rewrite tup_tup_com: term_db.

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
| tvar y => if (eqb_at y x) then u else tvar y
| dvar k => dvar k
| tconstr c l => tconstr c (map (tsubs x u) l)
end.

Lemma tup_tsubs_com : forall k x u t,
  tup k (tsubs x u t) = tsubs x (tup k u) (tup k t).
Proof. term_induction t. Qed.
Hint Rewrite tup_tsubs_com : term_db.

Lemma ntsubs_tup_com : forall k u t,
  ntsubs (S k) (tup 0 u) (tup 0 t) = tup 0 (ntsubs k u t).
Proof. term_induction t ; rcauto.
now destruct n ; destruct k ; inversion Heq.
Qed.
Hint Rewrite ntsubs_tup_com : term_db.

Lemma ntsubs_z_tup : forall u t, ntsubs 0 u (tup 0 t) = t.
Proof. term_induction t.
now rewrite <- (map_id l) at 2 ; apply map_ext_in ; apply Forall_forall.
Qed.
Hint Rewrite ntsubs_z_tup : term_db.



(** ** Free variables *)

Fixpoint freevars t :=
match t with
| tvar x => x :: nil
| dvar _ => nil
| tconstr f l => flat_map freevars l
end.
Notation closed t := (freevars t = nil).

Lemma closed_nofreevars : forall t x, closed t -> ~ In x (freevars t).
Proof. intros t x Hc Hin ; now rewrite Hc in Hin. Qed.
Hint Resolve closed_nofreevars : term_db.

Lemma freevars_tup : forall k t, freevars (tup k t) = freevars t.
Proof. term_induction t. Qed.
Hint Rewrite freevars_tup : term_db.

Lemma freevars_ntsubs : forall n u, closed u -> forall t,
  freevars (ntsubs n u t) = freevars t.
Proof. term_induction t. Qed.
Hint Rewrite freevars_ntsubs using intuition ; fail : term_db.

Lemma nfree_tsubs : forall x u t, ~ In x (freevars t) -> tsubs x u t = t.
Proof. term_induction t ; try rcauto; f_equal.
rewrite <- flat_map_concat_map in H; apply notin_flat_map_Forall in H.
rewrite <- (map_id l) at 2; apply map_ext_in; intros v Hv.
specialize_Forall_all v; intuition.
Qed.
Hint Rewrite nfree_tsubs using try (intuition ; fail) ;
                               (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma ntsubs_tsubs_com : forall x v n u, ~ In x (freevars u) -> forall t,
  ntsubs n u (tsubs x v t) = tsubs x (ntsubs n u v) (ntsubs n u t).
Proof. term_induction t. Qed.
Hint Rewrite ntsubs_tsubs_com using try (intuition ; fail) ;
                                    (try apply closed_nofreevars) ; intuition ; fail : term_db.

Lemma tsubs_tsubs_com : forall x v y u, x <> y -> ~ In x (freevars u) -> forall t,
  tsubs y u (tsubs x v t) = tsubs x (tsubs y u v) (tsubs y u t).
Proof. term_induction t. Qed.
Hint Rewrite tsubs_tsubs_com using try (intuition ; fail) ;
                                   (try apply closed_nofreevars) ; intuition ; fail : term_db.




(* additional results *)


Lemma tsubs_tsubs_eq : forall x u v t, tsubs x u (tsubs x v t) = tsubs x (tsubs x u v) t.
Proof. term_induction t; repeat case_analysis; intuition. Qed.
Hint Rewrite tsubs_tsubs_eq : term_db.

Lemma freevars_tsubs_closed : forall x u, closed u -> forall t,
  freevars (tsubs x u t) = remove eq_at_dec x (freevars t).
Proof. term_induction t.
rewrite remove_concat, flat_map_concat_map, map_map; f_equal.
apply map_ext_in; intros v Hv; now specialize_Forall IHl with v.
Qed.
Hint Rewrite freevars_tsubs_closed using intuition ; fail : term_db.

Lemma freevars_tsubs : forall x y u t,
  In x (freevars (tsubs y u t)) -> In x (freevars u) \/ In x (freevars t).
Proof.
term_induction t.
revert IHl; induction l; simpl; intros Hl Hin.
- inversion Hin.
- inversion Hl; subst.
  rewrite_all in_app_iff; intuition.
Qed.


(* Simultaneous substitution *)

Definition multi_tsubs L t := fold_left (fun F p => tsubs (fst p) (snd p) F) L t.

Lemma multi_tsubs_dvar : forall L n, multi_tsubs L (dvar n) = dvar n.
Proof. now induction L; intros n; simpl; [ | rewrite IHL ]. Qed.

Lemma multi_tsubs_nvar : forall L x, ~ In x (map fst L) -> multi_tsubs L (tvar x) = tvar x.
Proof.
induction L; intros x Hin; simpl; [ reflexivity | ].
destruct a; simpl; case_analysis.
- exfalso.
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
- case_analysis.
  + rewrite multi_tsubs_nvar by assumption; simpl.
    now rewrite eqb_refl.
  + rewrite nfree_tsubs; [ reflexivity | ].
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

End Terms.

