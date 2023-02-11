(* First-Order Formulas *)

From Quantifiers Require Export foterms.

Set Implicit Arguments.


(** * First-Order Formulas *)

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

Hint Resolve tesubs_ext : term_db.
Hint Resolve closed_notvars : term_db.

Context { fatom : Type }.  (* relation symbols for [formula] *)
(* Generic sets of connectives *)
Context { NCon : Type }. (* nullary connectives *)
Context { UCon : Type }. (* unary connectives *)
Context { BCon : Type }. (* binary connectives *)
Context { QCon : Type }. (* quantifiers *)

(** formulas *)
(** first-order formulas *)
Inductive formula T :=
| fvar : fatom -> list (term T)-> formula T
| fnul : NCon -> formula T
| funa : UCon -> formula T -> formula T
| fbin : BCon -> formula T -> formula T -> formula T
| fqtf : QCon -> vatom -> formula T -> formula T.
Arguments fnul {T} _.
(* Nullary connectives in [NCon] and [fnul] are mostly redundant with [fvar f nil] *)

Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let ncon := fresh "ncon" in
  let ucon := fresh "ucon" in
  let bcon := fresh "bcon" in
  let qcon := fresh "qcon" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | ncon | ucon A ? | bcon A1 ? A2 ? | qcon xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try (apply (f_equal (fvar _)));
    try (induction ll as [ | tt lll IHll ]; simpl; intuition;
         rewrite IHll; f_equal; intuition)
  | try ((try f_equal); intuition; fail)
  | try (apply (f_equal (funa _))); intuition
  | try (apply (f_equal2 (fbin _))); intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail);
     try (now rcauto) ];
  try (now rcauto).


(** * Size of [formula] *)

Fixpoint fsize T (A : formula T) :=
match A with
| fvar _ _ => 1
| fnul _ => 1
| funa _ B => S (fsize B)
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
| funa ucon B => funa ucon (esubs r B)
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

Lemma esubs_comp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) A : A⟦r⟧⟦s⟧ = A⟦r ;; s⟧.
Proof. formula_induction A. Qed.
Hint Rewrite esubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma esubs_ext T1 T2 (r1 r2 : T1 -> term T2) : r1 ~ r2 -> forall A, A⟦r1⟧ = A⟦r2⟧.
Proof. formula_induction A. Qed.


(** * Formula substitution *)

(** substitutes [term] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint subs T x u (A : formula T) :=
match A with
| fvar X l => fvar X (map (tsubs x u) l)
| fnul ncon => fnul ncon
| funa ucon B => funa ucon (subs x u B)
| fbin bcon B C => fbin bcon (subs x u B) (subs x u C)
| fqtf qcon y B => fqtf qcon y (if (eqb y x) then B else subs x u B)
end.
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").

Lemma fsize_subs T : forall u x (A : formula T), fsize A[u//x] = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_subs : term_db.


(** * Additional results with variable eigen type *)

Lemma subs_esubs T1 T2 (r : T1 -> term T2): forall x u A, (forall n, closed (r n)) ->
  A[u//x]⟦r⟧ = A⟦r⟧[tesubs r u//x].
Proof. formula_induction A; simpl in H; rcauto. Qed.
Hint Rewrite subs_esubs using intuition; fail : term_db.


(* We restrict to [formula nat] *)
(** * Eigen variables *)

Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").

Lemma esubs_fup v A : A↑⟦v⇓⟧ = A.
Proof. rcauto. Qed.
Hint Rewrite esubs_fup : term_db.

Lemma felift_esubs u r : forall A, A⟦r⟧↑ = A↑⟦⇑[u]r⟧.
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
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let ncon := fresh "ncon" in
  let ucon := fresh "ucon" in
  let bcon := fresh "bcon" in
  let qcon := fresh "qcon" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | ncon | ucon A ? | bcon A1 ? A2 ? | qcon xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try (apply (f_equal (fvar _)));
    try (induction ll as [ | tt lll IHll ]; simpl; intuition;
         rewrite IHll; f_equal; intuition)
  | try ((try f_equal); intuition; fail)
  | try (apply (f_equal (funa _))); intuition
  | try (apply (f_equal2 (fbin _))); intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail);
     try (now rcauto) ];
  try (now rcauto).
