(* Definitions and properties of first-order terms *)
(*   with holes in [nat] for de Bruijn indices *)

(* arity check on length of list arguments: strictly positive occurrence problem *)
(* see [fot_vec.v] for alternative approach using vectors *)

Require Export PeanoNat List.


(** * Different kinds of atoms *)
Parameter tatom : Type. (* function symbols for [term] *)
Parameter tarity : tatom -> nat. (* arity of function symbols *)
Parameter vatom : Type. (* variables for quantification *)


(** * First-Order Terms *)

(* TODO 
Non strictly positive occurrence of "term" in "forall (f : tatom) (l : list term), length l = tarity f -> term".

Inductive term :=
| dvar : nat -> term
| tvar : vatom -> term
| tconstr : forall (f:tatom) (l : list term), length l = tarity f -> term.
*)

(* OK without length check *)
Inductive term :=
| dvar : nat -> term
| tvar : vatom -> term
| tconstr : forall (f:tatom) (l : list term), term.

