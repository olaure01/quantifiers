(* First-Order Formulas *)

Require Import Lia.
Require Import stdlib_more_dec.
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
Hint Rewrite (@multi_tsubs_nil vatom tatom) : term_db.

Hint Resolve (@tesubs_ext vatom tatom) : term_db.
Hint Resolve (@closed_notvars vatom tatom) : term_db.
Hint Resolve (@fclosed_no_tecapture vatom tatom) : term_db.


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

Hint Rewrite (@remove_snd_remove vatom (formula T)) : term_db.

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


(** ** No capture of [y] when susbtituted for [x] in [A] *)
Fixpoint no_capture_at x y A :=
match A with
| fvar _ _ => True
| fnul _ => True
| fbin _ B C => no_capture_at x y B /\ no_capture_at x y C
| fqtf qcon z B => x ∈ (fqtf qcon z B) -> no_capture_at x y B /\ y <> z
end.
Notation "y #[ x ] A" := (no_capture_at x y A) (at level 30, format "y  #[ x ]  A").

Lemma no_capture_subs_freevars : forall A x y u,
  x #[y] A -> y ∈ A -> In x (tvars u) -> x ∈ A[u//y].
Proof. formula_induction A; try in_solve.
- revert H0 H1; clear; induction l; intros Hin1 Hin2; simpl; intuition.
  simpl in Hin1.
  apply in_or_app; apply in_app_or in Hin1; destruct Hin1 as [Hin1|Hin1]; [left|right]; rcauto.
  apply tvars_tsubs; intuition.
- exfalso; now apply remove_In in H0.
- apply notin_remove; intuition.
  apply in_remove in H0; destruct H0 as [Hin Hneq].
  apply IHA; intuition.
Qed.

Lemma no_capture_subs : forall x y z t A, closed t ->
  y #[x] A -> y #[x] A[t//z].
Proof. formula_induction A; revert H1; case_analysis; try (intuition; fail); intros Hin.
apply (remove_incl eq_dt_dec) with (l2:= freevars A) in Hin; intuition.
intros z' Hz'; apply freevars_subs in Hz'; intuition.
now exfalso; revert H3; apply closed_notvars. (* TODO automatize? *)
Qed.

Lemma subs_subs : forall x u y v, x <> y -> closed v -> forall A,
  Forall (fun y => y #[x] A) (tvars u) -> A[u//x][v//y] = A[v//y][tsubs y v u//x].
Proof. induction A; simpl; intros Hnc; f_equal.
- rnow rewrite 2 map_map; apply map_ext; rcauto.
- apply IHA1; eapply Forall_impl; [ | eassumption ]; simpl; intuition.
- apply IHA2; eapply Forall_impl; [ | eassumption ]; simpl; intuition.
- repeat case_analysis; intuition.
  + destruct (in_dec eq_dt_dec y (tvars u));
     [ destruct (in_dec eq_dt_dec x (freevars A)) | ]; rcauto.
    exfalso.
    specialize_Forall Hnc with y; apply Hnc; intuition.
    now apply notin_remove.
  + destruct (in_dec eq_dt_dec x (freevars A)).
    * apply IHA.
      apply Forall_forall; intros z Hinz.
      specialize_Forall Hnc with z; apply Hnc.
      apply notin_remove; intuition.
    * rewrite 2 (nfree_subs x); [ reflexivity | | assumption ].
      intros Hin; apply n.
      rewrite freevars_subs_closed in Hin; [ | assumption ].
      now apply in_remove in Hin.
Qed.
Hint Rewrite subs_subs using intuition; fail : term_db.
(* [subs_subs_closed] is a corollary of [subs_subs]:
     Proof.
       intros x u y v Hneq Hcu Hcv A.
       apply subs_subs; intuition; rewrite Hcu; constructor.
     Qed.
   but the direct proof above is much simpler *)


(** ** All variables in [formula] *)
(* occurring (free or bound or for quantification) in a formula *)
Fixpoint fvars A :=
match A with
| fvar _ l => flat_map tvars l
| fnul _ => nil
| fbin _ B C => fvars B ++ fvars C
| fqtf _ x B => x :: fvars B
end.

Lemma freevars_fvars : forall A, incl (freevars A) (fvars A).
Proof. formula_induction A.
eapply incl_tran; [ apply incl_remove | ].
eapply incl_tran; [ apply IHA | intuition ].
Qed.
Hint Resolve freevars_fvars : term_db.

Lemma notin_subs_bivar : forall x y A, ~ In x (fvars A) -> A[tvar x//y][tvar y//x] = A.
Proof. formula_induction A.
- apply notin_tsubs_bivar.
  intros Hin; apply H; simpl; intuition.
- apply H; simpl; intuition.
- now apply nfree_subs; intros Hin; apply H; right; apply freevars_fvars. (* TODO automatize? *)
Qed.


(** * Iterated substitution *)

Definition multi_subs L A := fold_left (fun F '(x,u) => F[u//x]) L A.
Notation "A [[ L ]]" := (multi_subs L A) (at level 8, format "A [[ L ]]").

Lemma multi_subs_nil : multi_subs nil = id.
Proof. reflexivity. Qed.
Hint Rewrite multi_subs_nil : term_db.

Lemma multi_subs_fvar : forall L X l, (fvar X l)[[L]] = fvar X (map (multi_tsubs L) l).
Proof. induction L; intros X l; simpl.
- rcauto; now rewrite map_id.
- now destruct a; rewrite IHL, map_map.
Qed.
Hint Rewrite multi_subs_fvar : term_db.

Lemma multi_subs_fbin : forall bcon L A B,
 (fbin bcon A B)[[L]] = fbin bcon A[[L]] B[[L]].
Proof. now induction L; intros A B; simpl; [ | destruct a; rewrite IHL ]. Qed.
Hint Rewrite multi_subs_fbin : term_db.

Lemma multi_subs_fqtf : forall qcon L x A,
  (fqtf qcon x A)[[L]] = fqtf qcon x A[[remove_snd x L]].
Proof.
induction L; intros x A; simpl; [ reflexivity | destruct a; simpl ].
case_analysis; rewrite IHL; f_equal.
Qed.
Hint Rewrite multi_subs_fqtf : term_db.

Lemma closed_multi_subs : forall L A, freevars A = nil -> A[[L]] = A.
Proof.
induction L; intros A Hc; [ reflexivity | destruct a; simpl ].
(rnow rewrite nfree_subs); rewrite Hc in H; inversion H.
Qed.
Hint Rewrite closed_multi_subs using intuition; fail : term_db.

Lemma multi_subs_closed : forall L A,
  Forall (fun z => closed z) (map snd L) -> incl (freevars A) (map fst L) ->
  freevars A[[L]] = nil.
Proof.
induction L; simpl; intros A Hc Hf.
- now apply incl_nil_inv in Hf; subst.
- destruct a; simpl; simpl in Hc, Hf; inversion_clear Hc as [ | ? ? Hc2 HcF].
  apply IHL; intuition.
  intros z Hinz.
  rewrite freevars_subs_closed in Hinz by assumption.
  apply in_remove in Hinz; destruct Hinz as [Hinz Hneq].
  apply Hf in Hinz; inversion Hinz; [ exfalso | ]; intuition.
Qed.

Lemma multi_subs_freevars : forall L A,
  Forall (fun z => closed z) (map snd L) ->
  incl (freevars A[[L]]) (freevars A).
Proof.
induction L; intros A Hc x Hin; [ assumption | destruct a; simpl in Hc, Hin ].
inversion_clear Hc as [ | ? ? Hct HcF ].
apply IHL in Hin; trivial.
apply freevars_subs in Hin; destruct Hin as [ [Hin _] | ]; intuition.
exfalso; rewrite Hct in Hin; inversion Hin.
Qed.

Lemma multi_subs_subs : forall L x u,
  Forall (fun z => closed z) (map snd L) ->
  forall A, Forall (fun y => y #[x] A) (tvars u) ->
  A[u//x][[L]] = A[[L∖x]][multi_tsubs L u//x].
Proof.
induction L; simpl; intros x u Hc A Hb; [ reflexivity | destruct a; simpl; simpl in Hc ].
inversion_clear Hc as [ | ? ? Hct HcF ].
case_analysis; rewrite <- IHL; intuition; f_equal; rcauto.
- apply Forall_incl with (tvars u); intuition.
  apply incl_remove.
- apply Forall_incl with (tvars u).
  + apply incl_remove.
  + apply Forall_impl with (fun y => y #[x] A); trivial.
    intros a; now apply no_capture_subs.
Qed.
Hint Rewrite multi_subs_subs using intuition; fail : term_db.

Lemma multi_subs_remove : forall L A x,
  Forall (fun z => closed z) (map snd L) -> x ∉ A -> A[[L∖x]] = A[[L]].
Proof.
induction L; simpl; intros A x Hc Hin; [ reflexivity | destruct a; simpl; simpl in Hc ].
inversion_clear Hc as [ | ? ? Hct HcF ].
case_analysis; rcauto.
apply IHL; try assumption.
intros Hin2; apply Hin.
apply freevars_subs in Hin2.
destruct Hin2 as [ [Hin2 _] | [Hin2 _] ]; trivial.
exfalso; rewrite Hct in Hin2; inversion Hin2.
Qed.
Hint Rewrite multi_subs_remove using intuition; fail : term_db.

Lemma multi_subs_extend : forall L A,
  Forall (fun z => closed z) (map snd L) -> incl (freevars A) (map fst L) ->
  forall L', A[[L]] = A[[L ++ L']].
Proof.
intros L A Hcl Hsub L'.
unfold multi_subs at 2; rewrite fold_left_app.
rewrite closed_multi_subs
  with (A:= fold_left (fun F '(x,u) => F[u//x]) L A); trivial.
now apply multi_subs_closed.
Qed.

End Fixed_Eigen_Type.


Section Two_Eigen_Types.

Variable T1 T2 : Type.
Variable r : T1 -> term T2.

Notation "x ∈ A" := (In x (freevars A)) (at level 30).
Notation "x ∉ A" := (~ In x (freevars A)) (at level 30).
Notation fclosed := (forall n, closed (r n)).
Notation "A [ u // x ]" := (subs x u A) (at level 8, format "A [ u // x ]").
Notation "A [[ L ]]" := (multi_subs L A) (at level 8, format "A [[ L ]]").
Notation "y #[ x ] A" := (no_capture_at x y A) (at level 30, format "y  #[ x ]  A").

(** * Additional results with variable eigen type *)

Lemma freevars_esubs_fclosed : fclosed -> forall A, freevars A⟦r⟧ = freevars A.
Proof. formula_induction A.
- now rewrite IHA1, IHA2.
- now rewrite IHA.
Qed.
Hint Rewrite freevars_esubs_fclosed using intuition; fail : term_db.

Lemma no_capture_esubs : fclosed -> forall x y A, y #[x] A -> y #[x] A⟦r⟧.
Proof. formula_induction A. Qed.

Lemma fvars_esubs : forall A,
  incl (fvars A ++ freevars A⟦r⟧) (fvars A⟦r⟧).
Proof. formula_induction A; simpl; intros z Hin; try in_solve.
- revert Hin; induction l; simpl; intros Hin; try in_solve.
  apply in_app_or in Hin; destruct Hin as [Hin|Hin]; auto.
  apply in_or_app; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; [left|right]; intuition.
  now eapply tvars_tesubs.
- inversion_clear Hin; subst; intuition.
  apply in_cons, IHA.
  apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left|right]; auto.
  now apply in_remove in H.
Qed.

(** * No capture generated by [r] in [A] under virtual binders for [l] *)
Fixpoint no_ecapture_at lv A :=
match A with
| fvar X l => fold_right (fun t P => and (no_tecapture_at r lv t) P) True l
| fnul _ => True
| fbin _ B C => no_ecapture_at lv B /\ no_ecapture_at lv C
| fqtf _ z B => no_ecapture_at (z :: lv) B
end.
Notation "#[[ lv ]] A" := (no_ecapture_at lv A) (at level 30, format "#[[ lv ]]  A").

Lemma no_ecapture_less : forall A lv1 lv2, incl lv1 lv2 ->
  #[[lv2]] A -> #[[lv1]] A.
Proof. formula_induction A.
- apply Forall_fold_right in H0; apply Forall_fold_right.
  eapply Forall_impl; [ intros t; apply no_tecapture_less | ]; eassumption.
- eapply IHA1; eassumption.
- eapply IHA2; eassumption.
- eapply IHA; [ | eassumption ]; in_solve.
Qed.

Lemma fclosed_no_ecapture : fclosed -> forall A lv, #[[lv]] A.
Proof. formula_induction A. Qed.
Hint Resolve fclosed_no_ecapture : term_db.

Lemma no_ecapture_subs_nfree : forall x y u A,
  closed u -> #[[y::nil]] A[u//x] ->
  In y (tvars (tesubs r u)) -> x ∉ A.
Proof. formula_induction A; try in_solve; intros Hinx.
- apply Forall_fold_right in H0.
  rewrite <- flat_map_concat_map in Hinx.
  apply in_flat_map in Hinx; destruct Hinx as [ z [Hinzl Hinz] ].
  apply in_map with (f:= tsubs x u) in Hinzl.
  specialize_Forall H0 with (tsubs x u z).
  apply no_tecapture_subs_notin in H0; intuition.
- apply in_remove in Hinx; destruct Hinx as [Hin Hneq].
  revert H0; case_analysis; intros Hg; intuition.
  apply no_ecapture_less with (lv1:= y::nil) in Hg; [ intuition | in_solve ].
Qed.


Fixpoint not_egenerated x A :=
match A with
| fvar X l => fold_right (fun t P => and (no_tecapture_at r (x::nil) t) P) True l
| fnul _ => True
| fbin _ B C => not_egenerated x B /\ not_egenerated x C
| fqtf _ z B => x <> z -> not_egenerated x B
end.

Lemma no_ecapture_not_egenerated : forall x A, #[[x::nil]] A -> not_egenerated x A.
Proof. formula_induction A.
apply no_ecapture_less with (lv1:= x::nil) in H; [ intuition | in_solve ].
Qed.
Hint Resolve no_ecapture_not_egenerated : term_db.

Lemma esubs_freevars : forall x A, not_egenerated x A -> x ∈ A⟦r⟧ -> x ∈ A.
Proof. formula_induction A; try in_solve.
- rewrite flat_map_map in H0; apply in_flat_map in H0; destruct H0 as [ t [Htin Hint] ].
  apply Forall_fold_right in H; specialize_Forall H with t.
  apply tesubs_tvars in Hint; intuition.
  rewrite <- flat_map_concat_map; apply in_flat_map; exists t; intuition.
- apply in_remove in H0; destruct H0 as [Hin Hneq].
  apply notin_remove; intuition.
Qed.

Lemma subs_esubs : forall x u A, not_egenerated x A ->
  A[u//x]⟦r⟧ = A⟦r⟧[tesubs r u//x].
Proof. formula_induction A; simpl in H; rcauto. Qed.
Hint Rewrite subs_esubs using try (intuition; fail);
                             (try apply no_ecapture_not_egenerated); try (intuition; fail);
                             (try apply fclosed_no_ecapture); intuition; fail : term_db.

Lemma multi_subs_esubs : forall L A, fclosed ->
  A[[L]]⟦r⟧ = A⟦r⟧[[map (fun '(x,u) => (x, tesubs r u)) L]].
Proof. induction L; simpl; intros A Hc; [ reflexivity | ].
destruct a; rewrite IHL, subs_esubs; intuition.
Qed.
Hint Rewrite multi_subs_esubs : term_db.

Lemma no_ecapture_esubs_subs_closed : forall u x A,
  closed u -> #[[nil]] A[u//x] -> not_egenerated x A ->
  Forall (fun z => z #[x] A⟦r⟧) (tvars (tesubs r u)).
Proof. formula_induction A.
- now apply Forall_forall.
- now apply Forall_forall.
- apply Forall_and; intuition.
- revert H0; case_analysis; intros H0.
  + apply Forall_forall; intros z Hz Hin.
    exfalso; now apply in_remove in Hin.
  + assert (Hx0 := H0).
    apply no_ecapture_less with (lv1:= nil) in H0; [ | in_solve ].
    apply IHA in H0; intuition.
    apply Forall_forall; intros z Hz Hin.
    specialize_Forall H0 with z; split; [ assumption | ].
    intros Heq2; subst.
    apply in_remove in Hin; destruct Hin as [Hin _].
    apply esubs_freevars in Hin; intuition.
    apply no_ecapture_subs_nfree in Hx0; intuition.
Qed.

End Two_Eigen_Types.


(* We restrict to [formula nat] *)
Section Eigen_nat.

Hint Rewrite freevars_esubs_fclosed using intuition; fail : term_db.

(** * Eigen variables *)

Fixpoint eigen_max A :=
match A with
| fvar _ l => list_max (map teigen_max l)
| fnul _ => 0
| fbin _ B C => max (eigen_max B) (eigen_max C)
| fqtf _ _ B => eigen_max B
end.

Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").
Notation "v ⇓" := (fesubs v) (at level 18, format "v ⇓").

Lemma freevars_fup : forall A, freevars A↑ = freevars A.
Proof. rcauto. Qed.
Hint Rewrite freevars_fup : term_db.

Lemma esubs_fup v A : A↑⟦v⇓⟧ = A.
Proof. now rewrite esubs_comp, (esubs_ext (fesubs_fup v)), esubs_evar. Qed.
Hint Rewrite esubs_fup : term_db.

Lemma lift_esubs u r : forall A, A⟦r⟧↑ = A↑⟦⇑[u]r⟧.
Proof. intros; rewrite 2 esubs_comp; apply esubs_ext, felift_comp. Qed.
Hint Rewrite lift_esubs : term_db.

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

