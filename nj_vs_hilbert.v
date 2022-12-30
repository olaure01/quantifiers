(* Tight links between Natural Deduction and Hilbert System *)

From Coq Require Import Lia.
From OLlibs Require Import infinite List_more List_assoc.
Require Import hilbert2nj nj2hilbert.

Set Implicit Arguments.


Section NJvsH.

Context { vatom : InfDecType } { tatom fatom : Type }.

Arguments tvar {_} {_} {T} _.

Notation hterm := (@term vatom tatom Empty_set).
Notation hformula := (@formula vatom tatom fatom Nocon Nocon Icon Qcon Empty_set).
Notation r_h2n := (r_empty nat).
Notation term := (@term vatom tatom nat).
Notation formula := (@formula vatom tatom fatom Nocon Nocon Icon Qcon nat).
Notation n2h_term r := (@tesubs vatom tatom nat Empty_set r).
Notation n2h_formula r := (@esubs vatom tatom fatom Nocon Nocon Icon Qcon nat Empty_set r).
Notation h2n_term := (@tesubs vatom tatom Empty_set nat r_h2n).
Notation h2n_formula := (@esubs vatom tatom fatom Nocon Nocon Icon Qcon Empty_set nat r_h2n).

Hint Rewrite (@multi_tsubs_evar vatom tatom) : term_db.


(* * From Hilbert System to Natural Deduction *)

Notation xf := (@fresh vatom nil).

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

Lemma vars_to_nat_snd_NoDup : forall (A : hformula), NoDup (map snd (vars_to_nat (freevars A))).
Proof. intros A; rewrite vars_to_nat_snd; apply NoDup_rev, seq_NoDup. Qed.

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

Lemma no_tecapture_nthvar : forall t lv r lvn,
  (forall z, In z (map fst lvn) -> ~ In z lv) ->
  NoDup (map snd lvn) ->
  (forall i, In i (map snd lvn) -> In (r i, i) lvn) ->
  no_tecapture_at (fun x => tvar (r x) : term) lv
                  (multi_tsubs (map (fun '(x, i) => (x, evar i)) lvn) (h2n_term t)).
Proof. term_induction t.
- intros lv r lvn Hlv Hnd Hincl.
  revert Hnd Hincl Hlv; induction lvn;
    [ intros; reflexivity | destruct a; simpl; intros Hnd Hincl Hlv ].
  rnow case_analysis.
  + apply Forall_forall; intros z Hz Heq; destruct Heq; intuition; subst.
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
  rewrite map_map in Hu; apply in_map_iff in Hu; destruct Hu as [ v [Heq Hin] ]; subst.
  specialize_Forall IHl with v; apply IHl; intuition.
Qed.

Lemma no_ecapture_nthvar : forall A lv r lvn,
  (forall z, In z (map fst lvn) -> ~ In z lv)->
  NoDup (map snd lvn) ->
  (forall i, In i (map snd lvn) -> In (r i, i) lvn) ->
  no_ecapture_at (fun x => tvar (r x) : term) lv
                 (multi_subs (map (fun '(x, i) => (x, evar i)) lvn) (h2n_formula A)).
Proof. formula_induction A;
  [ rewrite multi_subs_fvar | rewrite multi_subs_fbin | rewrite multi_subs_fqtf ];
  simpl; f_equal; intuition.
- apply Forall_fold_right, Forall_forall; intros t Ht.
  rewrite map_map in Ht; apply in_map_iff in Ht; destruct Ht as [ u [Heq Hu] ]; subst.
  apply no_tecapture_nthvar; intuition.
- replace (remove_assoc x (map (fun '(x0, i) => (x0, evar i)) lvn))
     with (map (fun '(x0,i) => (x0, evar i : term)) (remove_assoc x lvn))
    by (clear; induction lvn; intuition; unfold remove_assoc; simpl;
        repeat case_analysis; f_equal; intuition).
  apply IHA.
  + intros z Hz Hinz.
    rewrite <- remove_assoc_remove in Hz; apply in_remove in Hz.
    inversion Hinz; subst; intuition.
    apply H with z; intuition.
  + now apply NoDup_remove_assoc_snd.
  + intros i Hin; apply NoDup_remove_assoc_in; intuition.
    apply snd_remove_assoc in Hin; intuition.
Qed.

Lemma hilbert_vs_nj_term : forall t r lvn,
  NoDup (map snd lvn) ->
  (forall i, In i (map snd lvn) -> In (r i, i) lvn) ->
  n2h_term (fun x => tvar (r x))
           (multi_tsubs (map (fun '(x,i) => (x, evar i)) lvn) (h2n_term t)) = t.
Proof. term_induction t.
- intros r lvn Hnd Hincl.
  revert Hnd Hincl; induction lvn; [ intros; reflexivity | destruct a; simpl; intros Hnd Hincl ].
  rnow case_analysis.
  + specialize Hincl with n.
    assert (Heq := eq_refl n); eapply or_introl in Heq;
      apply Hincl in Heq; destruct Heq as [Heq|Heq].
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
  n2h_formula (fun x => tvar (r x))
              (multi_subs (map (fun '(x,i) => (x, evar i)) lvn) (h2n_formula A)) = A.
Proof. formula_induction A;
  [ rewrite multi_subs_fvar | rewrite multi_subs_fbin | rewrite multi_subs_fqtf ];
  simpl; f_equal; intuition.
- rewrite 2 map_map; rewrite <- (map_id l) at 2; apply map_ext_in; intros t Ht.
  now apply hilbert_vs_nj_term.
- replace (remove_assoc x (map (fun '(x0, i) => (x0, evar i)) lvn))
     with (map (fun '(x0,i) => (x0, evar i : term)) (remove_assoc x lvn))
    by (clear; induction lvn; intuition; unfold remove_assoc; simpl;
        repeat case_analysis; f_equal; intuition).
  apply IHA.
  + now apply NoDup_remove_assoc_snd.
  + intros i Hin; apply NoDup_remove_assoc_in; intuition.
    apply snd_remove_assoc in Hin; intuition.
Qed.

Proposition hilbert_vs_nj : forall A,
  { L : _ & hprove A -> prove nil (multi_subs L (h2n_formula A))
          & prove nil (multi_subs L (h2n_formula A)) -> hprove A }.
Proof.
intros A; exists (map (fun '(x,i) => (x, evar i)) (vars_to_nat (freevars A))); intros pi.
- apply h2n; intuition.
  + apply Forall_forall; intros t Ht.
    rewrite map_map in Ht.
    now apply in_map_iff in Ht; destruct Ht as [ u [Heq Hu] ]; subst; destruct u; simpl.
  + intros z Hz.
    rewrite map_map; apply in_map_iff.
    remember (freevars A) as l; revert z Hz; clear; induction l;
      intros z Hz; inversion_clear Hz; subst.
    * exists (z, length l); split; simpl; intuition.
    * apply IHl in H; destruct H as [ (y,n) [Heq Hin] ]; simpl in Heq; subst.
      exists (z, n); split; simpl; intuition.
- apply n2h with (r:= fun x => tvar (nthvar_nat (freevars A) x)) in pi.
  + simpl s2f in pi.
    rewrite hilbert_vs_nj_formula in pi; [ assumption | | ].
    * apply vars_to_nat_snd_NoDup.
    * apply vars_to_nat_content.
  + clear; repeat constructor.
    apply no_ecapture_nthvar; intuition.
    * apply vars_to_nat_snd_NoDup.
    * now apply vars_to_nat_content.
Qed.


(* * From Natural Deduction to Hilbert System *)

Definition freshterms l n := tvar (freshlist l n) : hterm.

Lemma no_tecapture_freshterms : forall t lv l, incl (l ++ tvars t) lv ->
  no_tecapture_at (freshterms lv) l t.
Proof. term_induction t.
- intros lv l' Hincl.
  apply Forall_forall; intros x Hx; intuition; subst.
  rewrite app_nil_r in Hincl; apply Hincl in Hx.
  revert Hx; apply freshlist_fresh.
- apply Forall_fold_right, Forall_forall; intros u Hu.
  specialize_Forall IHl with u; apply IHl.
  intros z Hz.
  apply H.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; intuition.
  apply in_flat_map; exists u; intuition.
Qed.

Lemma no_ecapture_freshterms : forall (A : formula) lv l, incl (l ++ fvars A) lv ->
  no_ecapture_at (freshterms lv) l A.
Proof. formula_induction A.
- apply Forall_fold_right, Forall_forall; intros t Ht.
  apply no_tecapture_freshterms.
  intros z Hz; apply H.
  apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left|right]; intuition.
  apply in_flat_map; exists t; intuition.
- apply IHA1; intros z Hz; apply H; in_solve.
- apply IHA2; intros z Hz; apply H; in_solve.
- apply IHA; intros z Hz; apply H; in_solve.
Qed.

Definition freshvars_to_nat (l : list vatom) n :=
  map (fun k => (freshlist l k, evar k : term)) (rev (seq 0 n)).

Lemma freshvars_to_nat_S : forall l n,
  freshvars_to_nat l (S n) = (freshlist l n, evar n) :: freshvars_to_nat l n.
Proof. now intros l n; unfold freshvars_to_nat; rewrite seq_S, rev_unit. Qed.

Lemma freshvars_to_nat_fst : forall l n,
  map fst (freshvars_to_nat l n) = rev (map (fun k => freshlist l k) (seq 0 n)).
Proof.
intros l n; rewrite <- map_rev; induction n; intuition.
unfold freshvars_to_nat.
rewrite seq_S, rev_unit; simpl; f_equal.
apply IHn.
Qed.

Lemma freshvars_to_nat_tcover : forall t lv n,
  incl (tvars t) lv -> teigen_max t < n -> 
  incl (tvars (n2h_term (freshterms lv) t)) (tvars t ++ map fst (freshvars_to_nat lv n)).
Proof. term_induction t.
- intros lv k Hincl He z Hz.
  inversion Hz; [ | inversion H]; subst.
  assert (In n (seq 0 k)) by (apply in_seq; lia).
  apply in_map with (f:= freshlist lv) in H.
  now rewrite freshvars_to_nat_fst, in_rev, rev_involutive.
- intros z Hz.
  rewrite <- flat_map_concat_map in Hz.
  apply in_flat_map in Hz; destruct Hz as [ u [Huin Hinu] ].
  specialize_Forall IHl with u.
  apply IHl with (n:= n) in Hinu.
  + apply in_or_app; apply in_app_or in Hinu; destruct Hinu as [Hinu|Hinu]; [left| now right].
    rewrite <- flat_map_concat_map; apply in_flat_map; exists u; intuition.
  + intros y Hy.
    apply H.
    apply in_flat_map; exists u; intuition.
  + apply list_max_lt in H0.
    * apply in_map with (f:= teigen_max) in  Huin.
      now specialize_Forall H0 with (teigen_max u).
    * intros Heq.
      destruct l; inversion Huin; simpl in Heq; inversion Heq.
Qed.

Lemma freshvars_to_nat_cover : forall A lv n,
  incl (fvars A) lv -> eigen_max A < n -> 
  incl (freevars (n2h_formula (freshterms lv) A)) (freevars A ++ map fst (freshvars_to_nat lv n)).
Proof. formula_induction A; intros z Hz.
- rewrite map_map, <- flat_map_concat_map in Hz;
    apply in_flat_map in Hz; destruct Hz as [ t [Htin Hint] ].
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
- apply in_remove in Hz; destruct Hz as [Hz Hneq].
  apply IHA with (n:= n) in Hz; intuition.
  + apply in_or_app; apply in_app_or in Hz; destruct Hz as [Hz|Hz]; [left| now right].
    now apply in_in_remove.
  + intros y Hy; apply H; in_solve.
Qed.

Lemma nj_vs_hilbert_term : forall n lv t,
  teigen_max t < n -> incl (tvars t) lv ->
  multi_tsubs (freshvars_to_nat lv n) (h2n_term (n2h_term (freshterms lv) t)) = t.
Proof. term_induction t.
- intros Hmax _; revert Hmax; clear; induction n; simpl; intros Hmax; try lia.
  rewrite freshvars_to_nat_S; simpl.
  destruct (Nat.eq_dec n0 n); subst.
  + rewrite eqb_refl; clear.
    enough (forall k, n <= k -> multi_tsubs (freshvars_to_nat lv n) (evar k) = evar k)
      as HI by (apply HI; lia).
    induction n; simpl; intros k Hlt; intuition.
    rewrite freshvars_to_nat_S; simpl; apply IHn; lia.
  + case_analysis.
    * exfalso.
      apply n1; now apply freshlist_inj with (l:= lv).
    * apply IHn; lia.
- intros Hmax Hlv.
  assert (In x lv) as Hlv2 by (now apply Hlv; left).
  revert Hlv2; clear; induction n; simpl; intros Hlv; intuition.
  rewrite freshvars_to_nat_S; simpl; case_analysis; [ exfalso | intuition ].
  revert Hlv; apply freshlist_fresh.
- rewrite multi_tsubs_tconstr; f_equal.
  rewrite map_map; rewrite <- (map_id l) at 2; apply map_ext_in; intros u Hu.
  specialize_Forall IHl with u; apply IHl.
  + apply list_max_lt in H.
    * apply in_map with (f:= teigen_max) in Hu.
      now specialize_Forall H with (teigen_max u).
    * intros Heq; destruct l; inversion Hu; simpl in Heq; inversion Heq.
  + intros z Hz; apply H0; now apply in_flat_map; exists u.
Qed.

Lemma nj_vs_hilbert_formula : forall n lv A,
  eigen_max A < n -> incl (fvars A) lv ->
  multi_subs (freshvars_to_nat lv n) (h2n_formula (n2h_formula (freshterms lv) A)) = A.
Proof. formula_induction A; 
  [ rewrite multi_subs_fvar | rewrite multi_subs_fbin | rewrite multi_subs_fqtf ]; f_equal.
- rewrite 2 map_map; rewrite <- (map_id l) at 2; apply map_ext_in; intros t Ht.
  apply nj_vs_hilbert_term.
  + apply list_max_lt in H.
    * apply in_map with (f:= teigen_max) in Ht.
      now specialize_Forall H with (teigen_max t).
    * intros Heq; destruct l; inversion Ht; simpl in Heq; inversion Heq.
  + intros z Hz; apply H0; now apply in_flat_map; exists t.
- apply IHA1; [ lia | intros z Hz; apply H0; in_solve ].
- apply IHA2; [ lia | intros z Hz; apply H0; in_solve ].
- enough (remove_assoc x (freshvars_to_nat lv n) = freshvars_to_nat lv n) as Heq.
  { rewrite Heq; apply IHA; intuition.
    intros z Hz; apply H0; in_solve. }
  assert (In x lv) as Hin by (apply H0; intuition).
  assert (0 < n) as Hn by lia.
  revert Hn; clear - Hin; induction n; simpl; intros Hn; try lia.
  unfold freshvars_to_nat.
  rewrite seq_S, rev_unit; simpl.
  case_analysis.
  + exfalso; revert Hin; apply freshlist_fresh.
  + f_equal. destruct n; [ reflexivity | apply IHn; lia ].
Qed.

Proposition nj_vs_hilbert : forall A, freevars A = nil ->
  { r : _ & prove nil A -> hprove (n2h_formula r A)
          & hprove (n2h_formula r A) -> prove nil A }.
(* closedness hypothesis on [A] required because of formulas like
   (∀x.P x) ⟶ P y or (∀x.∀y.P x) ⟶ P y *)
Proof.
intros A; exists (freshterms (fvars A)); intros pi.
- change A with (s2f nil A).
  apply n2h; intuition.
  simpl; repeat constructor.
  apply no_ecapture_freshterms.
  intros z Hz; in_solve.
- rewrite <- nj_vs_hilbert_formula with (S (eigen_max A)) (fvars A) _; [ | lia | now intros z Hz ].
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
