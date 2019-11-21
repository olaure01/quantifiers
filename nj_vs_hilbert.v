Require Import Lia.
Require Import stdlib_more.
Require Import hilbert2nj nj2hilbert.


Section NJvsH.

Context { vatom : InfDecType } { tatom : Type } { fatom : Type }.
Notation vfresh := (@fresh vatom).
Notation vfresh_prop := (@fresh_prop vatom).
Notation term := (@term vatom tatom).
Notation closed t := (freevars t = nil).
Notation tup := (@tup vatom tatom).
Notation hterm := (@hterm vatom tatom).
Notation hclosed t := (hfreevars t = nil).
Notation formula := (@formula vatom tatom fatom).
Notation hformula := (@hformula vatom tatom fatom).
Notation n2h_term := (@n2h_term vatom tatom).
Notation n2h_formula := (@n2h_formula vatom tatom fatom).
Notation h2n_term := (@h2n_term vatom tatom).
Notation h2n_formula := (@h2n_formula vatom tatom fatom).

Hint Rewrite
  (@tup_tup_com vatom tatom) (@tup_tsubs_com vatom tatom)
  (@ntsubs_tup_com vatom tatom) (@ntsubs_z_tup vatom tatom)
  (@freevars_tup vatom tatom) (@tsubs_tsubs_eq vatom tatom) : term_db.
Hint Resolve (@closed_nofreevars vatom tatom) : term_db.
Hint Rewrite (@freevars_ntsubs vatom tatom) using intuition; fail : term_db.
Hint Rewrite (@nfree_tsubs vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@ntsubs_tsubs_com vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@tsubs_tsubs_com vatom tatom)
  using try (intuition; fail); (try apply closed_nofreevars); intuition; fail : term_db.
Hint Rewrite (@freevars_tsubs_closed vatom tatom)
  using intuition; fail : term_db.

Ltac formula_induction A :=
  (try intros until A) ;
  let XX := fresh "X" in
  let xx := fresh "x" in
  let A1 := fresh A in
  let A2 := fresh A in
  let ll := fresh "l" in
  let lll := fresh "l" in
  let tt := fresh "t" in
  let IHll := fresh "IHl" in
  induction A as [ XX ll | A1 ? A2 ? | xx A | xx A ]; simpl; intros;
  [ rewrite ? flat_map_concat_map;
    try f_equal; try (induction ll as [ | tt lll IHll ]; simpl; intuition;
                      rewrite IHll; f_equal; intuition)
  | try (f_equal; intuition)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail)
  | try (repeat case_analysis; intuition; f_equal; intuition; (rnow idtac); fail) ];
  try (now (rnow idtac)); try (now rcauto).

Ltac term_induction t :=
  (try intros until t);
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  apply (term_ind_list_Forall t);
  [ intros nn; try (now intuition); simpl
  | intros xx; try (now intuition); simpl
  | intros cc ll IHll; simpl;
    rewrite ? flat_map_concat_map; rewrite ? map_map;
    try f_equal;
    try (apply map_ext_in; intros i Hi; specialize_Forall_all i);
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i);
    try (now intuition) ];
  try (now (rnow idtac)); try (now rcauto).

Ltac hterm_induction t :=
  (try intros until t);
  let nn := fresh "n" in
  let xx := fresh "x" in
  let cc := fresh "c" in
  let ll := fresh "l" in
  let IHll := fresh "IHl" in
  let i := fresh "i" in
  let Hi := fresh "Hi" in
  apply (hterm_ind_list_Forall t);
  [ intros xx; try (now intuition); simpl
  | intros cc ll IHll; simpl;
    rewrite ? flat_map_concat_map; rewrite ? map_map;
    try f_equal;
    try (apply map_ext_in; intros i Hi; specialize_Forall_all i);
    try (apply Forall_forall; intros i Hi; specialize_Forall_all i);
    try (now intuition) ];
  try (now (rnow idtac)); try (now rcauto).


(* * From Hilbert System to Natural Deduction *)

Lemma NoDup_remove_snd2 {T} x (L : list (vatom * T)) : forall f i,
  NoDup (map snd L) ->
  (In i (map snd L) -> In (f i, i) L) ->
  In i (map snd (remove_snd x L)) ->
  In (f i, i) (remove_snd x L).
Proof.
intros f i Hnd Hincl Hin.
apply remove_snd_notin; [ | apply snd_remove_snd in Hin; intuition ].
intros Heq; subst.
revert Hnd Hincl Hin; clear; induction L; [ intuition | ].
destruct a; simpl.
intros Hnd Hincl; inversion_clear Hnd; case_analysis; intros Hin; subst.
- apply IHL; intuition.
  exfalso; inversion H4; subst; intuition.
- destruct Hin as [Hin|Hin]; subst.
  + assert (Hin := eq_refl i); eapply or_introl in Hin; apply Hincl in Hin.
    destruct Hin as [Hin|Hin].
    * inversion Hin; subst; intuition.
    * apply H; now apply in_map with (f:= snd) in Hin.
  + apply IHL in Hin; intuition.
    exfalso; apply Heq; now inversion H4.
Qed.

Notation xf := (vfresh nil).
Definition vars_to_nat l :=
  ((fix f n s : list (vatom * nat) :=
    match s with
    | nil => nil
    | h :: tl => (h, n) :: f (pred n) tl
    end)
  (pred (length l)) l).

Lemma vars_to_nat_fst : forall l, map fst (vars_to_nat l) = l.
Proof. now induction l; intuition; simpl; f_equal. Qed.

Lemma vars_to_nat_snd : forall l, map snd (vars_to_nat l) = rev (seq 0 (length l)).
Proof. now induction l; intuition; simpl length; rewrite seq_S, rev_unit; simpl; f_equal. Qed.

Lemma vars_to_nat_snd_NoDup : forall (A : hformula), NoDup (map snd (vars_to_nat (hffreevars A))).
Proof. intros A; rewrite vars_to_nat_snd; apply NoDup_rev, NoDup_seq. Qed.

Definition nthvar_nat l := fun n => nth (length l - S n) l xf.

Lemma vars_to_nat_content : forall l n,
  In n (map snd (vars_to_nat l)) -> In (nthvar_nat l n, n) (vars_to_nat l).
Proof.
induction l; intros n Hin; [ assumption | ].
unfold vars_to_nat in Hin; simpl in Hin; fold (vars_to_nat l) in Hin.
destruct Hin as [Heq|Hin]; subst.
- unfold nthvar_nat.
  replace (length (a :: l) - S (length l)) with 0 by (simpl; lia); simpl; intuition.
- apply IHl in Hin.
  apply in_map with (f:= snd) in Hin; simpl in Hin.
  rewrite vars_to_nat_snd in Hin.
  assert (n < length l) as Hlt by (apply in_rev, in_seq in Hin; lia).
  unfold vars_to_nat; simpl; fold (vars_to_nat l); right.
  unfold nthvar_nat.
  replace (length (a :: l) - S n) with (S (length l - S n)) by (simpl; lia); simpl.
  apply IHl; now rewrite vars_to_nat_snd.
Qed.

Lemma ltgood_for_nthvar : forall t lv r lvn,
  (forall z, In z (map fst lvn) -> ~ In z lv) ->
  NoDup (map snd lvn) ->
  (forall i, In i (map snd lvn) -> In (r i, i) lvn) ->
  ltgood_for (fun x : nat => hvar (r x)) lv (multi_tsubs (map (fun '(x, i) => (x, dvar i)) lvn) (h2n_term t)).
Proof. hterm_induction t; intros lv r lvn Hlv Hnd Hincl.
- revert Hnd Hincl Hlv; induction lvn; [ intros; reflexivity | destruct a; simpl; intros Hnd Hincl Hlv ].
  case_analysis.
  + rewrite multi_tsubs_closed; [ | reflexivity ]; simpl; f_equal.
    apply Forall_forall; intros z Hz Heq; destruct Heq; intuition; subst.
    assert (Heq:= eq_refl n); eapply or_introl in Heq; apply Hincl in Heq.
    destruct Heq as [Heq|Hin].
    * inversion Heq; subst.
      apply Hlv with (r n); intuition.
    * apply in_map with (f:= fst) in Hin; simpl in Hin.
      apply Hlv with (r n); intuition.
  + inversion_clear Hnd.
    apply IHlvn; intuition.
    * assert (Hin := H2).
      eapply or_intror in Hin; apply Hincl in Hin; destruct Hin as [Hin|Hin]; intuition.
      inversion Hin; subst; intuition.
    * apply Hlv with z; intuition.
- rewrite multi_tsubs_tconstr; simpl.
  apply Forall_fold_right, Forall_forall; intros u Hu.
  rewrite map_map in Hu; apply in_map_iff in Hu; destruct Hu as [v [Heq Hin]]; subst.
  specialize_Forall IHl with v; apply IHl; intuition.
Qed.

Lemma lgood_for_nthvar : forall A lv r lvn,
  (forall z, In z (map fst lvn) -> ~ In z lv)->
  NoDup (map snd lvn) ->
  (forall i, In i (map snd lvn) -> In (r i, i) lvn) ->
  lgood_for (fun x : nat => hvar (r x)) lv (multi_subs (map (fun '(x, i) => (x, dvar i)) lvn) (h2n_formula A)).
Proof. formula_induction A;
  [ rewrite multi_subs_var | rewrite multi_subs_imp | rewrite multi_subs_frl | rewrite multi_subs_exs ];
  simpl; f_equal; intuition.
- apply Forall_fold_right, Forall_forall; intros t Ht.
  rewrite map_map in Ht; apply in_map_iff in Ht; destruct Ht as [u [Heq Hu]]; subst.
  apply ltgood_for_nthvar; intuition.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  replace (remove_snd x (map (fun '(x0, i) => (x0, dvar i)) lvn))
     with (map (fun '(x0,i) => (x0, dvar i : term)) (remove_snd x lvn))
    by (clear; induction lvn; intuition; unfold remove_snd; repeat case_analysis; f_equal; intuition).
  apply IHA.
  + intros z Hz Hinz.
    rewrite <- remove_snd_remove in Hz; apply in_remove in Hz.
    inversion Hinz; subst; intuition.
    apply H with z; intuition.
  + now apply NoDup_remove_snd.
  + intros i Hin; apply NoDup_remove_snd2; intuition.
Qed.

Lemma hilbert_vs_nj_term : forall t r lvn,
  NoDup (map snd lvn) ->
  (forall i, In i (map snd lvn) -> In (r i, i) lvn) ->
  n2h_term (fun x => hvar (r x)) (multi_tsubs (map (fun '(x,i) => (x, dvar i)) lvn) (h2n_term t)) = t.
Proof. hterm_induction t; intros r lvn Hnd Hincl.
- revert Hnd Hincl; induction lvn; [ intros; reflexivity | destruct a; simpl; intros Hnd Hincl ].
  case_analysis.
  + rewrite multi_tsubs_closed; [ | reflexivity ]; simpl; f_equal.
    specialize Hincl with n.
    assert (Heq := eq_refl n); eapply or_introl in Heq; apply Hincl in Heq; destruct Heq as [Heq|Heq].
    * now inversion Heq; subst.
    * exfalso.
      inversion_clear Hnd; apply H.
      now apply in_map with (f:= snd) in Heq.
  + inversion_clear Hnd.
    apply IHlvn; intuition.
    assert (Hin := H2).
    eapply or_intror in Hin; apply Hincl in Hin; destruct Hin as [Hin|Hin]; intuition.
    inversion Hin; subst; intuition.
- rewrite multi_tsubs_tconstr; simpl; f_equal.
  rewrite 2 map_map; rewrite <- (map_id l) at 2; apply map_ext_in; intros u Hu.
  specialize_Forall IHl with u; apply IHl; intuition.
Qed.

Lemma hilbert_vs_nj_formula : forall A r lvn,
  NoDup (map snd lvn) ->
  (forall i, In i (map snd lvn) -> In (r i, i) lvn) ->
  n2h_formula (fun x => hvar (r x)) (multi_subs (map (fun '(x,i) => (x, dvar i)) lvn) (h2n_formula A)) = A.
Proof. formula_induction A;
  [ rewrite multi_subs_var | rewrite multi_subs_imp | rewrite multi_subs_frl | rewrite multi_subs_exs ];
  simpl; f_equal; intuition.
- rewrite 2 map_map; rewrite <- (map_id l) at 2; apply map_ext_in; intros t Ht.
  now apply hilbert_vs_nj_term.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  replace (remove_snd x (map (fun '(x0, i) => (x0, dvar i)) lvn))
     with (map (fun '(x0,i) => (x0, dvar i : term)) (remove_snd x lvn))
    by (clear; induction lvn; intuition; unfold remove_snd; repeat case_analysis; f_equal; intuition).
  apply IHA.
  + now apply NoDup_remove_snd.
  + intros i Hin; apply NoDup_remove_snd2; intuition.
Qed.

Lemma hilbert_vs_nj : forall A,
  { L : _ & hprove A -> prove nil (multi_subs L (h2n_formula A))
          & prove nil (multi_subs L (h2n_formula A)) -> hprove A }.
Proof.
intros A; exists (map (fun '(x,i) => (x, dvar i)) (vars_to_nat (hffreevars A))); intros pi.
- apply h2n; intuition.
  + apply Forall_forall; intros t Ht.
    rewrite map_map in Ht.
    now apply in_map_iff in Ht; destruct Ht as [u [Heq Hu]]; subst; destruct u; simpl.
  + intros z Hz.
    rewrite map_map; apply in_map_iff.
    remember (hffreevars A) as l; revert z Hz; clear; induction l; intros z Hz; inversion_clear Hz; subst.
    * exists (z, length l); split; simpl; intuition.
    * apply IHl in H; destruct H as [(y,n) [Heq Hin]]; simpl in Heq; subst.
      exists (z, n); split; simpl; intuition.
- apply n2h with (r:= fun x => hvar (nthvar_nat (hffreevars A) x)) in pi.
  + simpl s2f in pi.
    rewrite hilbert_vs_nj_formula in pi; [ assumption | | ].
    * apply vars_to_nat_snd_NoDup.
    * apply vars_to_nat_content.
  + clear; repeat constructor.
    apply lgood_for_nthvar; intuition.
    * apply vars_to_nat_snd_NoDup.
    * now apply vars_to_nat_content.
Qed.


(* * From Natural Deduction to Hilbert System *)

Fixpoint freshvars_list l n :=
  match n with
  | 0 => vfresh l :: nil
  | S k => let lv := freshvars_list l k in vfresh (lv ++ l) :: lv
  end.
Definition freshvars l n := hd (vfresh l) (freshvars_list l n).
Definition freshterms l n := hvar (freshvars l n) : hterm.

Lemma freshvars_list_fresh : forall l n x,
 In x (freshvars_list l n) -> ~ In x l.
Proof.
induction n; simpl; intros x Hin Hinl.
- destruct Hin; intuition.
  revert Hinl; subst; apply vfresh_prop.
- destruct Hin; subst.
  + apply vfresh_prop with (l := freshvars_list l n ++ l); in_solve.
  + now apply IHn in Hinl.
Qed.

Lemma freshvars_list_prefix : forall l n m, n < m -> exists l',
  l' <> nil /\ freshvars_list l m = l' ++ freshvars_list l n.
Proof. induction m; intros Hlt; [ lia | ].
destruct (Nat.eq_dec n m); subst.
- now exists (vfresh (freshvars_list l m ++ l) :: nil).
- assert (n < m) as Hlt2 by lia.
  apply IHm in Hlt2.
  destruct Hlt2 as [l' [_ Heq]].
  exists (vfresh (freshvars_list l m ++ l) :: l'); split ; [ | now rewrite <- app_comm_cons, <- Heq ].
  intros Hnil; inversion Hnil.
Qed.

Lemma freshvars_list_NoDup : forall l n, NoDup (freshvars_list l n).
Proof. induction n; simpl; constructor; intuition.
- constructor.
- apply vfresh_prop with (l := freshvars_list l n ++ l); in_solve.
Qed.

Lemma freshvars_fresh : forall l n, ~ In (freshvars l n) l.
Proof.
intros l n Hin.
assert (In (freshvars l n) (freshvars_list l n)) as Hin2
  by (unfold freshvars; destruct n; in_solve).
now apply freshvars_list_fresh in Hin2.
Qed.

Lemma freshvars_inj : forall l n m, freshvars l n = freshvars l m -> n = m.
Proof.
intros l.
enough (forall n m, n < m -> freshvars l n = freshvars l m -> n = m) as Hlt.
{ intros n m Heq.
  destruct (Compare_dec.lt_eq_lt_dec n m) as [C | C]; [ destruct C as [C | C] | ].
  - now apply Hlt; [ lia | ].
  - assumption.
  - symmetry; now apply Hlt; [ lia | ]. }
intros n m Hlt Heq; exfalso.
apply freshvars_list_prefix with (l:= l) in Hlt; destruct Hlt as [l' [Hnil Hprf]].
unfold freshvars in Heq; rewrite Hprf in Heq.
destruct l'; [ now apply Hnil | ]; simpl in Heq.
destruct n; simpl in Heq, Hprf; rewrite Heq in Hprf.
- assert (In c ((c :: l') ++ nil)) as Hin by intuition.
  revert Hin; apply NoDup_remove_2; rewrite <- app_comm_cons, <- Hprf.
  apply (freshvars_list_NoDup l m).
- assert (In c ((c :: l') ++ freshvars_list l n)) as Hin by intuition.
  revert Hin; apply NoDup_remove_2; rewrite <- app_comm_cons, <- Hprf.
  apply (freshvars_list_NoDup l m).
Qed.

Lemma ltgood_for_freshterms : forall t lv l, incl (l ++ freevars t) lv ->
  ltgood_for (freshterms lv) l t.
Proof. term_induction t; intros lv l' Hincl.
- apply Forall_forall; intros x Hx; intuition; subst.
  rewrite app_nil_r in Hincl; apply Hincl in Hx.
  revert Hx; apply freshvars_fresh.
- apply Forall_fold_right, Forall_forall; intros u Hu.
  specialize_Forall IHl with u; apply IHl.
  intros z Hz.
  apply Hincl; rewrite <- flat_map_concat_map.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; intuition.
  apply in_flat_map; exists u; intuition.
Qed.

Lemma lgood_for_freshterms : forall (A : formula) lv l, incl (l ++ allvars A) lv ->
  lgood_for (freshterms lv) l A.
Proof. formula_induction A.
- apply Forall_fold_right, Forall_forall; intros t Ht.
  apply ltgood_for_freshterms.
  intros z Hz; apply H.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; intuition.
  apply in_flat_map; exists t; intuition.
- apply IHA1; intros z Hz; apply H; in_solve.
- apply IHA2; intros z Hz; apply H; in_solve.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  apply IHA; intros z Hz; apply H; in_solve.
Qed.

Definition freshvars_to_nat l n :=
  map (fun k => (freshvars l k, dvar k : term)) (rev (seq 0 n)).

Lemma freshvars_to_nat_S : forall l n,
  freshvars_to_nat l (S n) = (freshvars l n, dvar n) :: freshvars_to_nat l n.
Proof. now intros l n; unfold freshvars_to_nat; rewrite seq_S, rev_unit. Qed.

Lemma freshvars_to_nat_fst : forall l n,
  map fst (freshvars_to_nat l n) = rev (map (fun k => freshvars l k) (seq 0 n)).
Proof.
intros l n; rewrite <- map_rev; induction n; intuition.
unfold freshvars_to_nat.
rewrite seq_S, rev_unit; simpl; f_equal.
apply IHn.
Qed.

Lemma freshvars_to_nat_tcover : forall t lv n,
  incl (freevars t) lv -> teigen_max t < n -> 
  incl (hfreevars (n2h_term (freshterms lv) t)) (freevars t ++ map fst (freshvars_to_nat lv n)).
Proof. term_induction t; intros lv k Hincl He z Hz.
- inversion Hz; [ | inversion H]; subst.
  assert (In n (seq 0 k)) by (apply in_seq; lia).
  apply in_map with (f:= freshvars lv) in H.
  now rewrite freshvars_to_nat_fst, in_rev, rev_involutive.
- rewrite flat_map_concat_map, map_map, <- flat_map_concat_map in Hz.
  apply in_flat_map in Hz; destruct Hz as [u [Huin Hinu]].
  specialize_Forall IHl with u.
  apply IHl with (n:= k) in Hinu.
  + apply in_or_app; apply in_app_or in Hinu; destruct Hinu as [Hinu|Hinu]; [left| now right].
    rewrite <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
  + intros y Hy.
    apply Hincl.
    rewrite <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
  + apply list_max_lt in He.
    * apply in_map with (f:= teigen_max) in  Huin.
      now specialize_Forall He with (teigen_max u).
    * intros Heq.
      destruct l; inversion Huin; simpl in Heq; inversion Heq.
Qed.

Lemma freshvars_to_nat_cover : forall A lv n,
  incl (allvars A) lv -> eigen_max A < n -> 
  incl (hffreevars (n2h_formula (freshterms lv) A)) (ffreevars A ++ map fst (freshvars_to_nat lv n)).
Proof. formula_induction A; intros z Hz.
- rewrite map_map, <- flat_map_concat_map in Hz; apply in_flat_map in Hz; destruct Hz as [t [Htin Hint]].
  apply freshvars_to_nat_tcover with (t:= t) (n:= n) in Hint.
  + apply in_or_app; apply in_app_or in Hint; destruct Hint as [Hint|Hint]; [left| now right].
    rewrite <- flat_map_concat_map; apply in_flat_map; exists t; intuition.
  + intros y Hy.
    apply H.
    apply in_flat_map; exists t; intuition.
  + apply list_max_lt in H0.
    * apply in_map with (f:= teigen_max) in  Htin.
      now specialize_Forall H0 with (teigen_max t).
    * intros Heq.
      destruct l; inversion Htin; simpl in Heq; inversion Heq.
- apply in_app_or in Hz; destruct Hz as [Hz|Hz].
  + apply IHA1 with (n:= n) in Hz; [ | intros y Hy; apply H | lia ]; try in_solve.
  + apply IHA2 with (n:= n) in Hz; [ | intros y Hy; apply H | lia ]; try in_solve.
- refine ?[mygoal]. Existential 1 := ?mygoal.
  apply in_remove in Hz; destruct Hz as [Hz Hneq].
  apply IHA with (n:= n) in Hz; intuition.
  + apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left| now right].
    now apply notin_remove.
  + intros y Hy; apply H; in_solve.
Qed.

Lemma nj_vs_hilbert_term : forall n lv t,
  teigen_max t < n -> incl (freevars t) lv ->
  multi_tsubs (freshvars_to_nat lv n) (h2n_term (n2h_term (freshterms lv) t)) = t.
Proof. term_induction t; intros Hmax Hlv.
- revert Hmax; clear; induction n; simpl; intros Hmax; try lia.
  rewrite freshvars_to_nat_S; simpl.
  destruct (Nat.eq_dec n0 n); subst.
  + rewrite eqb_refl; clear.
    enough (forall k, n <= k -> multi_tsubs (freshvars_to_nat lv n) (dvar k) = dvar k)
      as HI by (apply HI; lia).
    induction n; simpl; intros k Hlt; intuition.
    rewrite freshvars_to_nat_S; simpl; apply IHn; lia.
  + case_analysis.
    * exfalso.
      apply n1; now apply freshvars_inj with (l:= lv).
    * apply IHn; lia.
- assert (In x lv) as Hlv2 by (now apply Hlv; left).
  revert Hlv2; clear; induction n; simpl; intros Hlv; intuition.
  rewrite freshvars_to_nat_S; simpl; case_analysis; [ exfalso | intuition ].
  revert Hlv; apply freshvars_fresh.
- rewrite multi_tsubs_tconstr; f_equal.
  rewrite map_map; rewrite <- (map_id l) at 2; apply map_ext_in; intros u Hu.
  specialize_Forall IHl with u; apply IHl.
  + apply list_max_lt in Hmax.
    * apply in_map with (f:= teigen_max) in Hu.
      now specialize_Forall Hmax with (teigen_max u).
    * intros Heq; destruct l; inversion Hu; simpl in Heq; inversion Heq.
  + intros z Hz; apply Hlv; rewrite <- flat_map_concat_map; now apply in_flat_map; exists u.
Qed.

Lemma nj_vs_hilbert_formula : forall n lv A,
  eigen_max A < n -> incl (allvars A) lv ->
  multi_subs (freshvars_to_nat lv n) (h2n_formula (n2h_formula (freshterms lv) A)) = A.
Proof. formula_induction A; 
  [ rewrite multi_subs_var | rewrite multi_subs_imp | rewrite multi_subs_frl | rewrite multi_subs_exs ];
  f_equal.
- rewrite 2 map_map; rewrite <- (map_id l) at 2; apply map_ext_in; intros t Ht.
  apply nj_vs_hilbert_term.
  + apply list_max_lt in H.
    * apply in_map with (f:= teigen_max) in Ht.
      now specialize_Forall H with (teigen_max t).
    * intros Heq; destruct l; inversion Ht; simpl in Heq; inversion Heq.
  + intros z Hz; apply H0; now apply in_flat_map; exists t.
- apply IHA1; [ lia | intros z Hz; apply H0; in_solve ].
- apply IHA2; [ lia | intros z Hz; apply H0; in_solve ].
- refine ?[mygoal]. Existential 1 := ?mygoal.
  enough (remove_snd x (freshvars_to_nat lv n) = freshvars_to_nat lv n) as Heq.
  { rewrite Heq; apply IHA; intuition.
    intros z Hz; apply H0; in_solve. }
  assert (In x lv) as Hin by (apply H0; intuition).
  assert (0 < n) as Hn by lia.
  revert Hn; clear - Hin; induction n; simpl; intros Hn; try lia.
  unfold freshvars_to_nat.
  rewrite seq_S, rev_unit; simpl.
  case_analysis; intuition.
  +  exfalso; revert Hin; apply freshvars_fresh.
  + f_equal; destruct n; intuition.
Qed.

Lemma nj_vs_hilbert : forall A, ffreevars A = nil ->
  { r : _ & prove nil A -> hprove (n2h_formula r A)
          & hprove (n2h_formula r A) -> prove nil A }.
(* closedness hypothesis required because of formulas like (∀x.∀y.P x) ⟶ P y *)
Proof.
intros A; exists (freshterms (allvars A)); intros pi.
- change A with (s2f nil A).
  apply n2h; intuition.
  simpl; repeat constructor.
  apply lgood_for_freshterms.
  intros z Hz; in_solve.
- rewrite <- nj_vs_hilbert_formula with (S (eigen_max A)) (allvars A) _; [ | lia | now intros z Hz ].
  apply h2n; intuition.
  + apply Forall_forall; intros t.
    remember (eigen_max A) as n; clear; induction n; simpl; intros Hin.
    * destruct Hin; subst; intuition.
    * unfold freshvars_to_nat in Hin.
      rewrite seq_S, rev_unit in Hin; simpl in Hin; destruct Hin as [Hin|Hin]; subst; intuition.
  + rewrite <- (app_nil_l (map _ _)), <- H.
    apply freshvars_to_nat_cover; intuition.
Qed.

End NJvsH.

