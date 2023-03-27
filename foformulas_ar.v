(* First-Order Formulas *)

(* with arity checks *)

From Quantifiers Require Export foterms_ar.

Set Implicit Arguments.


(** * First-Order Formulas *)

Section Formulas.

Context {vatom : DecType} {tatom : Type} {tarity : tatom -> nat}.
Notation term := (@term vatom tatom tarity).
Arguments evar _ _ _ {T}.
Notation evar := (evar vatom tatom tarity).

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
Hint Rewrite (@tvars_tesubs_closed vatom tatom) using intuition; fail : term_db.
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

Hint Resolve tesubs_ext : term_db.
Hint Resolve closed_notvars : term_db.

Context {fatom : Type}.  (* relation symbols for [formula] *)
Context {farity : fatom -> nat}.  (* arity of relation symbols *)
(* Generic sets of connectives *)
Context {NCon : Type}. (* nullary connectives *)
Context {UCon : Type}. (* unary connectives *)
Context {BCon : Type}. (* binary connectives *)
Context {QCon : Type}. (* quantifiers *)

(** formulas *)
(** first-order formulas *)
Inductive formula T : nat -> Type :=
| frel X : formula T (farity X)
| fconstr (t : term T 0) {k} : formula T (S k) -> formula T k
| fnul : NCon -> formula T 0
| funa : UCon -> formula T 0 -> formula T 0
| fbin : BCon -> formula T 0 -> formula T 0 -> formula T 0
| fqtf : QCon -> vatom -> formula T 0 -> formula T 0.
Arguments frel {T} _.
Arguments fnul {T} _.
(* Nullary connectives in [NCon] and [fnul] are mostly redundant with [fvar f nil] *)

Ltac formula_induction A :=
  try (intros until A); (* to avoid name clashes in induction t *)
  let XX := fresh "X" in
  let xx := fresh "x" in
  let ncon := fresh "ncon" in
  let ucon := fresh "ucon" in
  let bcon := fresh "bcon" in
  let qcon := fresh "qcon" in
  let A1 := fresh A in
  let A2 := fresh A in
  let BB := fresh "B" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  induction A as [ XX | tt BB | ncon | ucon A ? | bcon A1 ? A2 ? | qcon xx A ]; simpl; intros;
  [ try ((try f_equal); intuition; fail)
  | try (apply (f_equal2 (fun x y => fconstr x y))); intuition
  | try ((try f_equal); intuition; fail)
  | try (apply (f_equal (funa _))); intuition
  | try (apply (f_equal2 (fbin _))); intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail);
     try (now rcauto) ];
  try (now rcauto).


(** * Size of [formula] *)

Fixpoint fsize T k (A : formula T k) :=
match A with
| frel _ => 1
| fconstr _ _ => 1
| fnul _ => 1
| funa _ B => S (fsize B)
| fbin _ B C => S (fsize B + fsize C)
| fqtf _ _ B => S (fsize B)
end.


(** * Substitution of eigen variables in [formula] *)

(** substitutes the [term] [r n] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint esubs T1 T2 k (r : T1 -> term T2 0) (A : formula T1 k) : formula T2 k :=
match A with
| frel X => frel X
| fconstr t B => fconstr ((tesubs r) t) (esubs r B)
| fnul ncon => fnul ncon
| funa ucon B => funa ucon (esubs r B)
| fbin bcon B C => fbin bcon (esubs r B) (esubs r C)
| fqtf qcon x B => fqtf qcon x (esubs r B)
end.
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").

Lemma fsize_esubs T1 T2 k : forall (r : T1 -> term T2 0) (A : formula T1 k), fsize A⟦r⟧ = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_esubs : term_db.

Lemma esubs_evar T k : forall (A : formula T k),
  A⟦evar⟧ = A.
Proof. formula_induction A. Qed.
Hint Rewrite esubs_evar : term_db.

Lemma esubs_comp T1 T2 T3 k (r : T1 -> term T2 0) (s : T2 -> term T3 0) :
  forall A : formula T1 k, A⟦r⟧⟦s⟧ = A⟦r ;; s⟧.
Proof. formula_induction A. Qed.
Hint Rewrite esubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma esubs_ext T1 T2 k (r1 r2 : T1 -> term T2 0) : r1 ~ r2 -> forall A : formula T1 k, A⟦r1⟧ = A⟦r2⟧.
Proof. formula_induction A. Qed.


(** * Formula substitution *)

(** substitutes [term] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint subs T k x u (A : formula T k) : formula T k :=
match A with
| frel X => frel X
| fconstr t B => fconstr (tsubs x u t) (subs x u B)
| fnul ncon => fnul ncon
| funa ucon B => funa ucon (subs x u B)
| fbin bcon B C => fbin bcon (subs x u B) (subs x u C)
| fqtf qcon y B => fqtf qcon y (if eq_dt_dec y x then B else subs x u B)
end.
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").

Lemma fsize_subs T k : forall u x (A : formula T k), fsize A[u//x] = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_subs : term_db.


(** * Additional results with variable eigen type *)

Lemma subs_esubs T1 T2 k (r : T1 -> term T2 0): forall x u (A : formula T1 k),
  (forall n, closed (r n)) -> A[u//x]⟦r⟧ = A⟦r⟧[tesubs r u//x].
Proof. formula_induction A. Qed.
Hint Rewrite subs_esubs using intuition; fail : term_db.


(* We restrict to [formula nat] *)
(** * Eigen variables *)

Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").

Lemma esubs_fup k v (A : formula nat k) : A↑⟦v⇓⟧ = A.
Proof. rcauto. Qed.
Hint Rewrite esubs_fup : term_db.

Lemma felift_esubs k u r (A : formula nat k) : A↑⟦⇑[u]r⟧ = A⟦r⟧↑.
Proof. rcauto. Qed.
Hint Rewrite felift_esubs : term_db.

End Formulas.


(* Some sets of connectives *)
Inductive Nocon := .
Inductive Icon := imp_con.
Inductive Qcon := frl_con | exs_con.

Notation imp := (fbin imp_con).
Notation frl := (fqtf frl_con).
Notation exs := (fqtf exs_con).


Ltac formula_induction A :=
  try (intros until A); (* to avoid name clashes in induction t *)
  let XX := fresh "X" in
  let xx := fresh "x" in
  let ncon := fresh "ncon" in
  let ucon := fresh "ucon" in
  let bcon := fresh "bcon" in
  let qcon := fresh "qcon" in
  let A1 := fresh A in
  let A2 := fresh A in
  let BB := fresh "B" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  induction A as [ XX | tt BB | ncon | ucon A ? | bcon A1 ? A2 ? | qcon xx A ]; simpl; intros;
  [ try ((try f_equal); intuition; fail)
  | try (apply (f_equal2 (fun x y => fconstr x y))); intuition
  | try ((try f_equal); intuition; fail)
  | try (apply (f_equal (funa _))); intuition
  | try (apply (f_equal2 (fbin _))); intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail);
     try (now rcauto) ];
  try (now rcauto).
