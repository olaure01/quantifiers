(* First-Order Formulas *)

Require Import Lia.
Require Import stdlib_more.
Require Export foterms.

Set Implicit Arguments.


(** * First-Order Formulas *)
(* parametrized by a set of binary connectives and a set of unary quantifiers *)

Section Formulas.

Context { vatom : DecType } { tatom : Type }.
Notation term := (@term vatom tatom).
Arguments evar _ _ {T}.
Notation evar := (evar vatom tatom).

Notation "r ;; s" := (fecomp r s) (at level 20, format "r  ;;  s").
Notation closed t := (tvars t = nil).
Notation "⇑" := fup.
Notation "⇑[ u ] r" := (felift u r) (at level 25, format "⇑[ u ] r").

Hint Rewrite (@tesubs_evar vatom tatom) : term_db.
Hint Rewrite (@tesubs_comp vatom tatom) : term_db.
Hint Rewrite (@tsubs_tsubs_eq vatom tatom) : term_db.
Hint Rewrite (@tsubs_tsubs vatom tatom)
                        using try (intuition; fail);
                             (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@tvars_tesubs_fclosed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@tvars_tsubs_closed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@notin_tsubs vatom tatom)
                         using try easy;
                              (try (intuition; fail));
                              (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@notin_tsubs_bivar vatom tatom)
                               using try easy;
                                    (try (intuition; fail));
                                    (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@tsubs_tesubs vatom tatom) using try (intuition; fail) : term_db.

Hint Resolve (@tesubs_ext vatom tatom) : term_db.
Hint Resolve (@closed_notvars vatom tatom) : term_db.


Context { fatom : Type }.  (* relation symbols for [formula] *)
(* Generic sets of connectives (thanks to D.Pous for the suggestion) *)
Context { NCon : Type }. (* nullary connectives *)
Context { BCon : Type }. (* binary connectives *)
Context { QCon : Type }. (* quantifiers *)

(** formulas *)
(** first-order formulas *)
Inductive formula T :=
| fvar : fatom -> list (term T)-> formula T
| fnul : NCon -> formula T
| fbin : BCon -> formula T -> formula T -> formula T
| fqtf : QCon -> vatom -> formula T -> formula T.
Arguments fnul {T} _.
(* Nullary connectives in [NCon] and [fnul] are mostly redundant with [fvar f nil] *)

Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let ncon := fresh "ncon" in
  let bcon := fresh "bcon" in
  let qcon := fresh "qcon" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | ncon | bcon A1 ? A2 ? | qcon xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try (apply (f_equal (fvar _)));
    try (induction ll as [ | tt lll IHll ]; simpl; intuition;
         rewrite IHll; f_equal; intuition)
  | try ((try f_equal); intuition; fail)
  | try (apply (f_equal2 (fbin _))); intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail); 
     try (now rcauto) ];
  try (now rcauto).


(** * Size of [formula] *)

Fixpoint fsize T (A : formula T) :=
match A with
| fvar _ _ => 1
| fnul _ => 1
| fbin _ B C => S (fsize B + fsize C)
| fqtf _ _ B => S (fsize B)
end.


(** * Substitution of eigen variables in [formula] *)

(** substitutes the [term] [r n] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint esubs T1 T2 (r : T1 -> term T2) (A : formula T1) :=
match A with
| fvar X l => fvar X (map (tesubs r) l)
| fnul ncon => fnul ncon
| fbin bcon B C => fbin bcon (esubs r B) (esubs r C)
| fqtf qcon x B => fqtf qcon x (esubs r B)
end.
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").

Lemma fsize_esubs T1 T2 : forall (r : T1 -> term T2) A, fsize A⟦r⟧ = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_esubs : term_db.

Lemma esubs_evar T : forall (A : formula T),
  A⟦evar⟧ = A.
Proof. formula_induction A. Qed.
Hint Rewrite esubs_evar : term_db.

Lemma esubs_comp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) :
  forall A, A⟦r⟧⟦s⟧ = A⟦r ;; s⟧.
Proof. formula_induction A. Qed.
Hint Rewrite esubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma esubs_ext T1 T2 (r1 r2 : T1 -> term T2) :
  r1 == r2 -> forall A, A⟦r1⟧ = A⟦r2⟧.
Proof. formula_induction A. Qed.


Section Fixed_Eigen_Type.

Variable T : Type.
Arguments tvar {_} {_} {T} _.
Arguments tvars {_} {_} {T} _.
Implicit Type A : formula T.

(** * Formula substitution *)

(** substitutes [term] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint subs x u A :=
match A with
| fvar X l => fvar X (map (tsubs x u) l)
| fnul ncon => fnul ncon
| fbin bcon B C => fbin bcon (subs x u B) (subs x u C)
| fqtf qcon y B => fqtf qcon y (if (eqb y x) then B else subs x u B)
end.
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").

Lemma fsize_subs : forall u x A, fsize A[u//x] = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_subs : term_db.

Lemma subs_subs_eq : forall x u v A, A[v//x][u//x] = A[tsubs x u v//x].
Proof. formula_induction A. Qed.
Hint Rewrite subs_subs_eq : term_db.


(** * Variables *)

(** ** Free variables in [formula] *)
Fixpoint freevars A :=
match A with
| fvar _ l => flat_map tvars l
| fnul _ => nil
| fbin _ B C => freevars B ++ freevars C
| fqtf _ x B => remove eq_dt_dec x (freevars B)
end.
Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "x ∉ A" := (~ In x (freevars A)) (at level 30).

Lemma freevars_qtf : forall qcon x y, y <> x -> forall A,
  x ∈ A -> x ∈ (fqtf qcon y A).
Proof. intros; apply notin_remove; intuition. Qed.

Lemma nfree_subs : forall x u A, x ∉ A -> A[u//x] = A.
Proof. formula_induction A.
- rnow apply notin_tsubs then apply H.
- rnow apply H.
- rcauto; rnow rewrite IHA.
  apply H, notin_remove; intuition.
Qed.
Hint Rewrite nfree_subs using intuition; fail : term_db.

Lemma subs_subs_closed : forall x u y v, x <> y -> closed u -> closed v ->
  forall A, A[u//x][v//y] = A[v//y][tsubs y v u//x].
Proof. formula_induction A. Qed.
Hint Rewrite subs_subs_closed using intuition; fail : term_db.

Lemma freevars_subs_closed : forall x u, closed u -> forall A,
  freevars A[u//x] = remove eq_dt_dec x (freevars A).
Proof. formula_induction A; rewrite ? remove_app; try now f_equal.
- now f_equal; apply tvars_tsubs_closed.
- symmetry; apply remove_remove_eq.
- now rewrite remove_remove_neq by (now intros Heq'; apply Heq); f_equal.
Qed.
Hint Rewrite freevars_subs_closed using intuition; fail : term_db.

Lemma freevars_subs : forall x y u A,
  x ∈ A[u//y] -> (In x (tvars u) /\ y ∈ A) \/ (x ∈ A /\ x <> y).
Proof. formula_induction A; try in_solve.
- revert H; induction l; simpl; intros Hin.
  + inversion Hin.
  + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    * apply tvars_tsubs in Hin; in_solve.
    * apply IHl in Hin; in_solve.
- revert H; case_analysis; intros H.
  + right; intuition.
    apply in_remove in H; intuition.
  + assert (Hin := proj1 (in_remove _ _ _ _ H)).
    apply IHA in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition;
      apply notin_remove; intuition.
    subst; revert H; apply remove_In.
Qed.

End Fixed_Eigen_Type.


Section Two_Eigen_Types.

Variable T1 T2 : Type.
Variable r : T1 -> term T2.

Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "x ∉ A" := (~ In x (freevars A)) (at level 30).
Notation fclosed := (forall n, closed (r n)).
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").

(** * Additional results with variable eigen type *)

Lemma freevars_esubs_fclosed : fclosed -> forall A, freevars A⟦r⟧ = freevars A.
Proof. formula_induction A.
- now rewrite IHA1, IHA2.
- now rewrite IHA.
Qed.
Hint Rewrite freevars_esubs_fclosed using intuition; fail : term_db.


Lemma subs_esubs : forall x u A, fclosed ->
  A[u//x]⟦r⟧ = A⟦r⟧[tesubs r u//x].
Proof. formula_induction A; simpl in H; rcauto. Qed.
Hint Rewrite subs_esubs using intuition; fail : term_db.

End Two_Eigen_Types.


(* We restrict to [formula nat] *)
Section Eigen_nat.

Hint Rewrite freevars_esubs_fclosed using intuition; fail : term_db.

(** * Eigen variables *)

Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").

Lemma freevars_fup : forall A, freevars A↑ = freevars A.
Proof. rcauto. Qed.
Hint Rewrite freevars_fup : term_db.

Lemma esubs_fup v A : A↑⟦v⇓⟧ = A.
Proof. now rewrite esubs_comp, (esubs_ext (fesubs_fup v)), esubs_evar. Qed.
Hint Rewrite esubs_fup : term_db.

Lemma felift_esubs u r : forall A, A⟦r⟧↑ = A↑⟦⇑[u]r⟧.
Proof. intros; rewrite 2 esubs_comp; apply esubs_ext, felift_comp. Qed.
Hint Rewrite felift_esubs : term_db.

End Eigen_nat.

End Formulas.

(* Some sets of connectives *)
Inductive Nocon := .
Inductive Icon := imp_con.
Inductive Qcon := frl_con | exs_con.

Notation imp := (fbin imp_con).
Notation frl := (fqtf frl_con).
Notation exs := (fqtf exs_con).


Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let ncon := fresh "ncon" in
  let bcon := fresh "bcon" in
  let qcon := fresh "qcon" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | ncon | bcon A1 ? A2 ? | qcon xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try (apply (f_equal (fvar _)));
    try (induction ll as [ | tt lll IHll ]; simpl; intuition;
         rewrite IHll; f_equal; intuition)
  | try ((try f_equal); intuition; fail)
  | try (apply (f_equal2 (fbin _))); intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail); 
     try (now rcauto) ];
  try (now rcauto).

