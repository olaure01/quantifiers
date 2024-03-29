(* First-Order Terms with no Eigen Variable *)

From Quantifiers Require Export foterms.

Set Implicit Arguments.


Section Terms.

Context { vatom : DecType } { tatom : Type }.

Notation "r ;; s" := (fecomp r s) (at level 20, format "r  ;;  s").
Notation closed t := (tvars t = nil).
Notation rclosed r := (forall n, closed (r n)).

(* Function allowing to embed [term Empty_set] into any [term T]
     through identity embedding by using [tesubs (r_empty T)] *)
Definition r_empty T : Empty_set -> @term vatom tatom T := fun z => match z with end.

Lemma closed_r_empty T : rclosed (r_empty T).
Proof. intros []. Qed.
Hint Resolve closed_r_empty : term_db.

Lemma fecomp_r_empty T1 T2 s : r_empty T1 ;; s ~ r_empty T2.
Proof. intros []. Qed.
Hint Rewrite fecomp_r_empty : term_db.

End Terms.
