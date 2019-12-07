(* First-Order Formulas *)

Require Import Lia.
Require Import stdlib_more.
Require Export foterms.

Set Implicit Arguments.


(* Preliminary results on lists of pairs *)

Fixpoint remove_snd {T1 : DecType} {T2} x (L : list (T1 * T2)) :=
match L with
| nil => nil
| (y, F) :: TL => if eqb x y then remove_snd x TL else (y, F) :: remove_snd x TL
end.
Notation "L ∖ x" := (remove_snd x L) (at level 18).

Lemma remove_snd_remove {T1 : DecType} {T2} x (L : list (T1 * T2)) :
  remove eq_dt_dec x (map fst L) = map fst (remove_snd x L).
Proof.
induction L; simpl; [ reflexivity | rewrite IHL ]; destruct a; simpl.
repeat case_analysis; intuition.
Qed.

Lemma remove_snd_notin {T1 : DecType} {T2} x (L : list (T1 * T2)) :
  forall y a, x <> y -> In (y, a) L -> In (y, a) (remove_snd x L).
Proof.
induction L; simpl; intros y b Hneq Hin; [ assumption | destruct a ].
destruct Hin as [Hin|Hin]; case_analysis; intuition.
exfalso; apply Hneq.
now inversion Hin.
Qed.

Lemma snd_remove_snd  {T1 : DecType} {T2} x (L : list (T1 * T2)) :
  incl (map snd (remove_snd x L)) (map snd L).
Proof.
induction L; simpl; intros z Hz; intuition.
destruct a; simpl.
revert Hz; case_analysis; intros Hz; intuition.
Qed.

Lemma NoDup_remove_snd {T1 : DecType} {T2} x (L : list (T1 * T2)) :
  NoDup (map snd L) -> NoDup (map snd (remove_snd x L)).
Proof.
induction L; simpl; intros Hnd; [ constructor | destruct a ].
inversion_clear Hnd.
case_analysis; intuition.
constructor; intuition.
apply snd_remove_snd in H2.
now apply H.
Qed.






(** * First-Order Formulas *)
(* parametrized by a set of binary connectives and a set of unary quantifiers *)

Section Formulas.

Context { vatom : DecType } { tatom : Type }.
Notation term := (@term vatom tatom).

Notation "r ;; s" := (fdbcomp r s) (at level 20, format "r  ;;  s").
Notation "x ∉ r" := (forall n, ~ In x (tvars (r n))) (at level 30).
Notation closed t := (tvars t = nil).
Notation rclosed r := (forall n, closed (r n)).
Notation "⇑" := tup.
Notation "↑ r" := (fdblift r) (at level 25, format "↑ r").

Hint Rewrite (@tdbsubs_comp vatom tatom) : term_db.
Hint Rewrite (@tsubs_tsubs_eq vatom tatom) : term_db.
Hint Rewrite (@tsubs_tsubs vatom tatom) using try (intuition; fail);
                                             (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@tvars_tdbsubs_closed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@tvars_tsubs_closed vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@notin_tsubs vatom tatom)
                         using try easy;
                              (try (intuition; fail));
                              (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@notin_tsubs_bivar vatom tatom)
                               using try easy;
                                    (try (intuition; fail));
                                    (try apply closed_notvars); intuition; fail : term_db.
Hint Rewrite (@tsubs_tdbsubs vatom tatom)
                           using try (intuition; fail);
                                (try apply rclosed_notvars); intuition; fail : term_db.
Hint Rewrite (@multi_tsubs_nil vatom tatom) : term_db.

Hint Resolve (@tdbsubs_ext vatom tatom) : term_db.
Hint Resolve (@closed_notvars vatom tatom) : term_db.


Context { fatom : Type }.  (* relation symbols for [formula] *)
Context { BCon : Type }. (* binary connectives *)
Context { QCon : Type }. (* quantifiers *)

(** formulas *)
(** first-order formulas *)
Inductive formula T :=
| fvar : fatom -> list (term T)-> formula T
| fbin : BCon -> formula T -> formula T -> formula T
| fqtf : QCon -> vatom -> formula T -> formula T.

Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let bcon := fresh "bcon" in
  let qcon := fresh "qcon" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | bcon A1 ? A2 ? | qcon xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try (apply (f_equal (fvar _)));
    try (induction ll as [ | tt lll IHll ]; simpl; intuition;
         rewrite IHll; f_equal; intuition)
  | try (apply (f_equal2 (fbin _)));
    intuition
  | (try apply (f_equal (fqtf _ _))); repeat case_analysis; try (intuition; fail); 
     try (intuition; (rnow idtac); fail) ];
  try (now (rnow idtac)); try (now rcauto).


(** * Size of [formula] *)

Fixpoint fsize T (A : formula T) :=
match A with
| fvar _ _ => 1
| fbin _ B C => S (fsize B + fsize C)
| fqtf _ _ B => S (fsize B)
end.


(** * Substitution of eigen variables in [formula] *)

(** substitutes the [term] [r n] for index [n] in [formula] [A] *)
(* capture is not avoided *)
Fixpoint dbsubs T1 T2 (r : T1 -> term T2) (A : formula T1) :=
match A with
| fvar X l => fvar X (map (tdbsubs r) l)
| fbin bcon B C => fbin bcon (dbsubs r B) (dbsubs r C)
| fqtf qcon x B => fqtf qcon x (dbsubs r B)
end.
Notation "A ⟦ r ⟧" := (dbsubs r A) (at level 8, left associativity, format "A ⟦ r ⟧").

Lemma fsize_dbsubs T1 T2 : forall (r : T1 -> term T2) A, fsize A⟦r⟧ = fsize A.
Proof. formula_induction A. Qed.
Hint Rewrite fsize_dbsubs : term_db.

Lemma dbsubs_comp T1 T2 T3 (r : T1 -> term T2) (s : T2 -> term T3) :
  forall A, A⟦r⟧⟦s⟧ = A⟦r ;; s⟧.
Proof. formula_induction A. Qed.

(* the result of substitution depends extensionnaly on the substituting function *)
Lemma dbsubs_ext T1 T2 (r1 r2 : T1 -> term T2) :
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
| fbin _ B C => freevars B ++ freevars C
| fqtf _ x B => remove eq_dt_dec x (freevars B)
end.
Notation "x ∈ A" := (In x (freevars A)) (at level 30).

Lemma freevars_qtf : forall qcon x y, y <> x -> forall A,
  x ∈ A -> x ∈ (fqtf qcon y A).
Proof. intros; apply notin_remove; intuition. Qed.

Lemma freevars_dbsubs_closed : forall r, rclosed r -> forall A,
  freevars A⟦r⟧ = freevars A.
Proof. formula_induction A.
- now rewrite IHA1, IHA2.
- now rewrite IHA.
Qed.
Hint Rewrite freevars_dbsubs_closed using intuition; fail : term_db.

Lemma nfree_subs : forall x u A, ~ x ∈ A -> A[u//x] = A.
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

Lemma subs_dbsubs : forall x u r, x ∉ r -> forall A,
  A[u//x]⟦r⟧ = A⟦r⟧[tdbsubs r u//x].
Proof. formula_induction A. Qed.
Hint Rewrite subs_dbsubs using try (intuition ; fail) ;
                              (try apply closed_notvars) ; intuition ; fail : term_db.

(** ** No capture of [y] when susbtituted for [x] in [A] *)
Fixpoint no_capture_at x y A :=
match A with
| fvar X l => True
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
- now apply nfree_subs; intros Hin; apply H; right; apply freevars_fvars.
  (* TODO automatize? *)
Qed.


(** * Iterated substitution *)

Definition multi_subs L A := fold_left (fun F '(x,u) => F[u//x]) L A.
Notation "A [[ L ]]" := (multi_subs L A) (at level 8, format "A [[ L ]]").

Lemma multi_subs_nil : multi_subs nil = id.
Proof. reflexivity. Qed.
Hint Rewrite multi_subs_nil : term_db.

Lemma multi_subs_fvar : forall L X l, (fvar X l)[[L]] = fvar X (map (multi_tsubs L) l).
Proof. induction L; intros X l; simpl.
- rnow idtac then rewrite map_id.
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

Lemma multi_subs_dbsubs : forall L r A,
  Forall (fun x => x ∉ r) (map fst L) ->
  A[[L]]⟦r⟧ = A⟦r⟧[[map (fun '(x,u) => (x, tdbsubs r u)) L]].
Proof. induction L; simpl; intros r A HF; [ reflexivity | ].
destruct a; simpl in HF; inversion_clear HF.
now rewrite IHL, subs_dbsubs.
Qed.
Hint Rewrite multi_subs_dbsubs : term_db.

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
  Forall (fun z => closed z) (map snd L) -> ~ x ∈ A ->
  A[[L∖x]] = A[[L]].
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

Lemma multi_subs_ext : forall L A,
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


(* We restrict to [formula nat] *)
Section Eigen_nat.

(** * Eigen variables *)

Fixpoint eigen_max A :=
match A with
| fvar _ l => list_max (map teigen_max l)
| fbin _ B C => max (eigen_max B) (eigen_max C)
| fqtf _ _ B => eigen_max B
end.

Notation "A ↑" := (A⟦⇑⟧) (at level 8, format "A ↑").

Lemma lift_dbsubs r : forall A, A⟦r⟧↑ = A↑⟦↑r⟧.
Proof. intros; rewrite 2 dbsubs_comp; apply dbsubs_ext, fdblift_comp. Qed.
Hint Rewrite lift_dbsubs : term_db.

End Eigen_nat.

End Formulas.

