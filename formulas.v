(* Formulas with separated first- and second-order quantifiers *)

From Coq Require Import Lia.
From OLlibs Require Import List_more.
From Quantifiers Require Export foterms_ext.

Set Implicit Arguments.


(** * Formulas *)

Section Formulas.

Context { vatom : DecType } { tatom : Type }.
Notation term := (@term vatom tatom).
Arguments evar _ _ {T}.
Notation evar := (evar vatom tatom).

Notation "r ;; s" := (fecomp r s) (at level 20, format "r  ;;  s").
Notation tclosed t := (tvars t = nil).
Notation rtclosed r := (forall n, tclosed (r n)).
Notation "⇑" := fup.
Notation "⇑[ u ] r" := (felift u r) (at level 25, format "⇑[ u ] r").

Hint Rewrite (@tesubs_evar vatom tatom) : term_db.
Hint Rewrite (@tesubs_comp vatom tatom) : term_db.
Hint Rewrite (@tsubs_tsubs_eq vatom tatom) : term_db.
Hint Rewrite (@tsubs_tsubs vatom tatom)
                        using try tauto;
                              try apply closed_notvars; tauto : term_db.
Hint Rewrite (@tvars_tesubs_closed vatom tatom) using tauto : term_db.
Hint Rewrite (@tvars_tsubs_closed vatom tatom) using tauto : term_db.
Hint Rewrite (@notin_tsubs vatom tatom)
                         using try easy; try tauto;
                               try apply closed_notvars; tauto: term_db.
Hint Rewrite (@notin_tsubs_bivar vatom tatom)
                               using try easy; try tauto;
                                     try apply closed_notvars; tauto : term_db.
Hint Rewrite (@tsubs_tesubs vatom tatom) using try tauto : term_db.

Hint Resolve tesubs_ext : term_db.
Hint Resolve closed_notvars : term_db.

Context { satom : DecType }.  (* second-order variables *)
Context { fatom : Type }.  (* relation symbols for [formula] *)
(* Generic sets of connectives *)
Context { NCon : Type }. (* nullary connectives *)
Context { UCon : Type }. (* unary connectives *)
Context { BCon : Type }. (* binary connectives *)
Context { QFCon : Type }. (* first-order quantifiers *)
Context { QSCon : Type }. (* second-order quantifiers *)

(** formulas *)
Inductive formula U T :=
| sevar : U -> formula U T
| svar : satom -> formula U T
| fvar : fatom -> list (term T)-> formula U T
| fnul : NCon -> formula U T
| funa : UCon -> formula U T -> formula U T
| fbin : BCon -> formula U T -> formula U T -> formula U T
| fqtf : QFCon -> vatom -> formula U T -> formula U T
| sqtf : QSCon -> satom -> formula U T -> formula U T.
Arguments sevar {U T} _.
Arguments svar {U T} _.
Arguments fvar {U T} _.
Arguments fnul {U T} _.
(* Nullary connectives in [NCon] and [fnul] are mostly redundant with [fvar f nil] *)

Ltac formula_induction A :=
  (try intros until A) ;
  let nn := fresh "n" in
  let RR := fresh "R" in
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
  let IH := fresh "IH" in
  let IH2 := fresh "IH" in
  induction A as [ n | XX | RR ll | ncon | ucon A IH | bcon A1 IH A2 IH2
                 | qcon xx A IH | qcon XX A IH ]; simpl; intros;
  [ try (apply (f_equal sevar)); try ((rnow idtac); fail)
  | try (apply (f_equal svar)); repeat case_analysis; try ((rnow idtac); fail)
  | rewrite ? flat_map_concat_map;
    try (apply (f_equal (fvar _)));
    try (induction ll as [ | tt lll IHll ]; simpl; intuition;
         rewrite IHll; f_equal; intuition)
  | try (try f_equal; intuition; fail)
  | try (apply (f_equal (funa _))); intuition
  | try (apply (f_equal2 (fbin _))); intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail); try now rcauto
  | (try apply (f_equal (sqtf _ _))); repeat case_analysis; try (intuition; fail); try now rcauto ];
  try (rewrite ? IH, ? IH2; reflexivity);
  try now rcauto.

(** * Atomic formulas *)

Inductive atomic U T : formula U T -> Prop :=
| atomic_sevar u : atomic (sevar u)
| atomic_svar X : atomic (svar X)
| atomic_fvar f l : atomic (fvar f l).


(** * Size of [formula] *)

Fixpoint fsize U T (A : formula U T) :=
match A with
| sevar _ | svar _ | fvar _ _ | fnul _ => 1
| funa _ B => S (fsize B)
| fbin _ B C => S (fsize B + fsize C)
| fqtf _ _ B | sqtf _ _ B => S (fsize B)
end.


(** * Free variables in [formula] *)

Fixpoint freevars U T (A : formula U T) :=
match A with
| sevar _ => nil
| svar _ => nil
| fvar _ l => flat_map (@tvars _ _ _) l
| fnul _ => nil
| funa _ B => freevars B
| fbin _ B C => freevars B ++ freevars C
| fqtf _ x B => remove eq_dt_dec x (freevars B)
| sqtf _ x B => freevars B
end.
Notation fclosed A := (freevars A = nil).
Notation rfclosed r := (forall n, fclosed (r n)).

Lemma fclosed_nofreevars U T (A : formula U T) x : fclosed A -> ~ In x (freevars A).
Proof. intros -> []. Qed.

Lemma rfclosed_nofreevars U1 U2 T (r : U1 -> formula U2 T) n x : rfclosed r -> ~ In x (freevars (r n)).
Proof. intros -> []. Qed.

Fixpoint sfreevars U T (A : formula U T) :=
match A with
| sevar _=> nil
| svar X => X :: nil
| fvar _ l => nil
| fnul _ => nil
| funa _ B => sfreevars B
| fbin _ B C => sfreevars B ++ sfreevars C
| fqtf _ x B => sfreevars B
| sqtf _ X B => remove eq_dt_dec X (sfreevars B)
end.
Notation sclosed A := (sfreevars A = nil).
Notation rsclosed r := (forall n, sclosed (r n)).

Lemma sclosed_nosfreevars U T (A : formula U T) X : sclosed A -> ~ In X (sfreevars A).
Proof. intros -> []. Qed.

Lemma rsclosed_nosfreevars U1 U2 T (r : U1 -> formula U2 T) n x : rsclosed r -> ~ In x (sfreevars (r n)).
Proof. intros -> []. Qed.


(** * Substitution of first-order eigen variables in [formula] *)

(** substitutes the [term] [r n] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint esubs U T1 T2 (r : T1 -> term T2) (A : formula U T1) :=
match A with
| sevar e => sevar e
| svar X => svar X
| fvar R l => fvar R (map (tesubs r) l)
| fnul ncon => fnul ncon
| funa ucon B => funa ucon (esubs r B)
| fbin bcon B C => fbin bcon (esubs r B) (esubs r C)
| fqtf qcon x B => fqtf qcon x (esubs r B)
| sqtf qcon X B => sqtf qcon X (esubs r B)
end.
Notation "A ⟦ r ⟧" := (esubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").

Lemma fsize_esubs U T1 T2 (r : T1 -> term T2) (A : formula U T1) : fsize A⟦r⟧ = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_esubs : term_db.

Lemma freevars_esubs_closed U T1 T2 (r : T1 -> term T2) (A : formula U T1) (Hc : rtclosed r) :
  freevars A⟦r⟧ = freevars A.
Proof. formula_induction A. Qed.
Hint Rewrite freevars_esubs_closed using tauto : term_db.

Lemma freevars_esubs U T1 T2 (r : T1 -> term T2) (A : formula U T1) : incl (freevars A) (freevars A⟦r⟧).
Proof. formula_induction A.
- clear. induction l as [|t l IHl]; cbn; [ intro; tauto | ].
  apply incl_app_app, IHl.
  apply tvars_tesubs.
- apply remove_incl. assumption.
Qed.
#[local] Hint Rewrite freevars_esubs : term_db.

Lemma sfreevars_esubs U T1 T2 (r : T1 -> term T2) (A : formula U T1) : sfreevars A⟦r⟧ = sfreevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite sfreevars_esubs : term_db.

Lemma esubs_evar U T (A : formula U T) : A⟦evar⟧ = A.
Proof. formula_induction A. Qed.
Hint Rewrite esubs_evar : term_db.

Lemma esubs_comp U T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) (A : formula U T1) :
  A⟦r⟧⟦s⟧ = A⟦r ;; s⟧.
Proof. formula_induction A. Qed.
Hint Rewrite esubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma esubs_ext U T1 T2 (r1 r2 : T1 -> term T2) : r1 ~ r2 -> forall A : formula U T1, A⟦r1⟧ = A⟦r2⟧.
Proof. formula_induction A. Qed.


(** * Formula substitution *)

(** ** Substitution of second-order eigen variables in [formula] *)

(** substitutes the [formula] [r n] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint essubs U1 U2 T (r : U1 -> formula U2 T) (A : formula U1 T) :=
match A with
| sevar e => r e
| svar X => svar X
| fvar R l => fvar R l
| fnul ncon => fnul ncon
| funa ucon B => funa ucon (essubs r B)
| fbin bcon B C => fbin bcon (essubs r B) (essubs r C)
| fqtf qcon x B => fqtf qcon x (essubs r B)
| sqtf qcon X B => sqtf qcon X (essubs r B)
end.
Notation "A ⟦ r ⟧2" := (essubs r A) (at level 8, left associativity, format "A ⟦ r ⟧2").

Definition fescomp U1 U2 U3 T (r : U1 -> formula U2 T) (s : U2 -> formula U3 T) := fun x => (r x)⟦s⟧2.
Notation "r ;2; s" := (fescomp r s) (at level 20, format "r  ;2;  s").

Lemma fsize_essubs U1 U2 T (r : U1 -> formula U2 T) A : fsize A <= fsize A⟦r⟧2.
Proof. formula_induction A; (try (destruct (r n))); cbn; lia. Qed.
Hint Rewrite fsize_essubs : term_db.

Lemma freevars_essubs_closed U1 U2 T (r : U1 -> formula U2 T) (A : formula U1 T) (Hc : rfclosed r) :
  freevars A⟦r⟧2 = freevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite freevars_essubs_closed : term_db.

Lemma sfreevars_essubs_closed U1 U2 T (r : U1 -> formula U2 T) (A : formula U1 T) (Hc : rsclosed r) :
  sfreevars A⟦r⟧2 = sfreevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite sfreevars_essubs_closed : term_db.

Lemma essubs_evar U T (A : formula U T) : A⟦sevar⟧2 = A.
Proof. formula_induction A. Qed.
Hint Rewrite essubs_evar : term_db.

Lemma essubs_comp U1 U2 U3 T (r : U1 -> formula U2 T) (s : U2 -> formula U3 T) A :
  A⟦r⟧2⟦s⟧2 = A⟦r ;2; s⟧2.
Proof. formula_induction A. Qed.
Hint Rewrite essubs_comp : term_db.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma essubs_ext U1 U2 T (r1 r2 : U1 -> formula U2 T) : r1 ~ r2 -> forall A, A⟦r1⟧2 = A⟦r2⟧2.
Proof. formula_induction A. Qed.


(** ** Substitution of first-order variables in [formula] *)

(** substitutes [term] [u] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint subs U T x u (A : formula U T) :=
match A with
| sevar n => sevar n
| svar X => svar X
| fvar X l => fvar X (map (tsubs x u) l)
| fnul ncon => fnul ncon
| funa ucon B => funa ucon (subs x u B)
| fbin bcon B C => fbin bcon (subs x u B) (subs x u C)
| fqtf qcon y B => fqtf qcon y (if (eqb y x) then B else subs x u B)
| sqtf qcon X B => sqtf qcon X (subs x u B)
end.
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").

Lemma fsize_subs U T u x (A : formula U T) : fsize A[u//x] = fsize A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite fsize_subs : term_db.

Lemma nfree_subs U T x u (A : formula U T) : ~ In x (freevars A) -> subs x u A = A.
Proof. formula_induction A.
- apply notin_tsubs. intro. apply H. in_solve.
- apply H. in_solve.
- apply IH. intro. apply H. apply in_in_remove; auto.
Qed.
#[local] Hint Rewrite nfree_subs using try tauto;
                                       try (apply fclosed_nofreevars; tauto);
                                       try apply rfclosed_nofreevars; tauto : term_db.


(** ** Substitution of second-order variables in [formula] *)

(** substitutes [formula] [F] for variable [x] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint ssubs U T X F (A : formula U T) :=
match A with
| sevar n => sevar n
| svar Y => if (eqb Y X) then F else (svar Y)
| fvar R l => fvar R l
| fnul ncon => fnul ncon
| funa ucon B => funa ucon (ssubs X F B)
| fbin bcon B C => fbin bcon (ssubs X F B) (ssubs X F C)
| fqtf qcon y B => fqtf qcon y (ssubs X F B)
| sqtf qcon Y B => sqtf qcon Y (if (eqb Y X) then B else ssubs X F B)
end.
Notation "A [ F // X ]2" := (ssubs X F A) (at level 8, format "A [ F // X ]2").

Lemma fsize_ssubs U T F X (A : formula U T) : fsize A <= fsize A[F//X]2.
Proof. formula_induction A; (try destruct F); cbn; lia. Qed.
#[local] Hint Rewrite fsize_ssubs : term_db.

Lemma fsize_ssubs_atomic U T F X (A : formula U T) : atomic F -> fsize A[F//X]2 = fsize A.
Proof. formula_induction A; (try destruct F; inversion H); cbn; lia. Qed.
#[local] Hint Rewrite fsize_ssubs_atomic : term_db.

(** ** Additional results with variable eigen type *)

Lemma nfree_ssubs U T X F (A : formula U T) : ~ In X (sfreevars A) -> A[F//X]2 = A.
Proof. formula_induction A. apply IH. intro. apply H. apply in_in_remove; auto. Qed.
#[local] Hint Rewrite nfree_ssubs using try tauto;
                                       try (apply sclosed_nosfreevars; tauto);
                                       try apply rsclosed_nosfreevars; tauto : term_db.

Lemma subs_esubs U T1 T2 (r : T1 -> term T2) x u (A : formula U T1): rtclosed r ->
  A[u//x]⟦r⟧ = A⟦r⟧[tesubs r u//x].
Proof. formula_induction A. Qed.
#[local] Hint Rewrite subs_esubs using tauto : term_db.

Lemma ssubs_esubs U T1 T2 (r : T1 -> term T2) X F (A : formula U T1): rtclosed r ->
  A[F//X]2⟦r⟧ = A⟦r⟧[F⟦r⟧//X]2.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite ssubs_esubs using tauto : term_db.

Lemma subs_essubs U1 U2 T (r : U1 -> formula U2 T) x u A (Hc : rfclosed r) : A[u//x]⟦r⟧2 = A⟦r⟧2[u//x].
Proof. formula_induction A. Qed.
#[local] Hint Rewrite subs_essubs using tauto : term_db.

Lemma ssubs_essubs U1 U2 T (r : U1 -> formula U2 T) X F A (Hc : rsclosed r) : A[F//X]2⟦r⟧2 = A⟦r⟧2[F⟦r⟧2//X]2.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite ssubs_essubs using tauto : term_db.


(* We restrict to [formula nat nat] *)
(** * Eigen variables *)

Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").

Lemma freevars_fup T (A : formula T nat) : freevars A↑ = freevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite freevars_fup : term_db.

Lemma sfreevars_fup T (A : formula T nat) : sfreevars A↑ = sfreevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite sfreevars_fup : term_db.

Lemma esubs_fup T v (A : formula T nat) : A↑⟦v⇓⟧ = A.
Proof. rcauto. Qed.
#[local] Hint Rewrite esubs_fup : term_db.

Lemma felift_esubs T u r (A : formula T nat) : A↑⟦⇑[u]r⟧ = A⟦r⟧↑.
Proof. rcauto. Qed.
#[local] Hint Rewrite felift_esubs : term_db.

Definition sfup T := fun n => @sevar nat T (S n).
Notation "⇑2" := (sfup nat).
Notation "A ↑2" := (A⟦⇑2⟧2) (at level 8, format "A ↑2").

Lemma fclosed_sfup : rfclosed ⇑2.
Proof. reflexivity. Qed.
Hint Rewrite fclosed_sfup : term_db.

Lemma sclosed_sfup : rsclosed ⇑2.
Proof. reflexivity. Qed.
Hint Rewrite sclosed_sfup : term_db.

Lemma fsize_sfup A : fsize A↑2 = fsize A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite fsize_sfup : term_db.

Lemma freevars_sfup A : freevars A↑2 = freevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite freevars_sfup : term_db.

Lemma sfreevars_sfup A : sfreevars A↑2 = sfreevars A.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite sfreevars_sfup : term_db.

Definition fessubs T (F : formula nat T) := fun n =>
  match n with
  | 0 => F
  | S n => sevar n
  end.
Notation "F ⇓2" := (fessubs F) (at level 18, format "F ⇓2").

Lemma fclosed_fessubs T (F : formula nat T) : fclosed F -> rfclosed (F⇓2).
Proof. now intros Hc [|]. Qed.
Hint Resolve fclosed_fessubs : term_db.

Lemma sclosed_fessubs T (F : formula nat T) : sclosed F -> rsclosed (F⇓2).
Proof. now intros Hc [|]. Qed.
Hint Resolve sclosed_fessubs : term_db.

Definition feslift F r := fun n =>
  match n with
  | 0 => F
  | S k => (r k)↑2
  end.
Notation "⇑2[ F ] r" := (feslift F r) (at level 25, format "⇑2[ F ] r").

Lemma fclosed_feslift F r : fclosed F -> rfclosed r -> rfclosed (⇑2[F]r).
Proof. rnow intros ? ? [|]. Qed.
Hint Resolve fclosed_feslift : term_db.

Lemma sclosed_feslift F r : sclosed F -> rsclosed r -> rsclosed (⇑2[F]r).
Proof. rnow intros ? ? [|]. Qed.
Hint Resolve sclosed_feslift : term_db.

Lemma essubs_fup F A : A↑2⟦F⇓2⟧2 = A.
Proof. rcauto. Qed.
#[local] Hint Rewrite essubs_fup : term_db.

Lemma felift_essubs (r : nat -> formula nat nat) A : A↑⟦fun n => (r n)↑⟧2 = A⟦r⟧2↑.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite felift_essubs : term_db.

Lemma feslift_esubs r (A : formula nat nat) : A↑2⟦r⟧ = A⟦r⟧↑2.
Proof. formula_induction A. Qed.
#[local] Hint Rewrite feslift_esubs : term_db.

Lemma feslift_essubs F r A : A↑2⟦⇑2[F]r⟧2 = A⟦r⟧2↑2.
Proof. rcauto. Qed.
#[local] Hint Rewrite feslift_essubs : term_db.

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
  let nn := fresh "n" in
  let RR := fresh "R" in
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
  let IH := fresh "IH" in
  let IH2 := fresh "IH" in
  induction A as [ n | XX | RR ll | ncon | ucon A IH | bcon A1 IH A2 IH2
                 | qcon xx A IH | qcon XX A IH ]; simpl; intros;
  [ try (apply (f_equal sevar)); try ((rnow idtac); fail)
  | try (apply (f_equal svar)); repeat case_analysis; try ((rnow idtac); fail)
  | rewrite ? flat_map_concat_map;
    try (apply (f_equal (fvar _)));
    try (induction ll as [ | tt lll IHll ]; simpl; intuition;
         rewrite IHll; f_equal; intuition)
  | try (try f_equal; intuition; fail)
  | try (apply (f_equal (funa _))); intuition
  | try (apply (f_equal2 (fbin _))); intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail); try now rcauto
  | (try apply (f_equal (sqtf _ _))); repeat case_analysis; try (intuition; fail); try now rcauto ];
  try (rewrite ? IH, ? IH2; reflexivity);
  try now rcauto.
