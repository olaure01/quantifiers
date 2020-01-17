(* First-Order Terms with no Eigen Variable *)

Require Import stdlib_more.
Require Export foterms.

Set Implicit Arguments.


Section Terms.

Context { vatom : DecType } { tatom : Type }.

Notation "r ;; s" := (fecomp r s) (at level 20, format "r  ;;  s").
Notation closed t := (tvars t = nil).
Notation fclosed r := (forall n, closed (r n)).

Arguments tvar {_} {_} {T} _.

(* Function allowing to embed [term Empty_set] into any [term T]
     through identity embedding by using [tesubs (r_empty T)] *)
Definition r_empty T : Empty_set -> @term vatom tatom T :=
  fun z => match z with end.

Lemma fclosed_r_empty T : fclosed (r_empty T).
Proof. intros n; destruct n. Qed.
Hint Resolve fclosed_r_empty : term_db.

Lemma fecomp_r_empty T1 T2 : forall s, r_empty T1 ;; s == r_empty T2.
Proof. intros s n; destruct n. Qed.
Hint Rewrite fecomp_r_empty : term_db.

End Terms.

