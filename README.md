# Formalizing Quantifiers

A formalization of quantifiers based on:

* formulas as first-order structures
* binding for quantifier rules implemented with de Bruijn indices

It applies to:

* first-order logics
* second-order propositional logics (a la system F for example)

Content:

* `fot.v`: definitions and properties of first-order terms
* `all1.v`: sequent calculus for _first-order_ Additive Linear Logic
* `all2.v`: sequent calculus for _second-order_ propositional Additive Linear Logic
* `nj1.v`: formulas and natural deduction for _first-order_ Intuitionistic Logic (normalization proof)
* `nj2.v`: formulas and natural deduction for propositional _second-order_ Intuitionistic Logic
* `all1.v`: sequent calculus for _first-order_ Additive Linear Logic (cut elimination proof)
* `all2.v`: sequent calculus for propositional _second-order_ Additive Linear Logic (cut elimination proof)

Variations:

* `*_ar.v`: terms with arity checks
* `*_vec.v`: terms with vector arguments to control arities

With **cut-elimination/normalization** proofs as main results.

Current examples are developed in Coq, but formalization does not depend on the surrounding meta-theory and should be adaptable to (any?) proof assistant.


