# Formalizing Quantifiers

A formalization of quantifiers based on:

* formulas as first-order structures (no alpha-equivalence)
* binding for quantifier rules implemented with de Bruijn indices

It applies to:

* first-order logics
* propositional second-order logics (a la system F for example)

Content:

* `stdlib_more.v`: various lemmas missing in the standard library
* `dectype.v`: types (including infinite ones) with Boolean equality
* `term_tactics.v`: some tactics used in following files


* `fot.v`: definitions and properties of first-order terms
* `all1.v`: sequent calculus for _first-order_ Additive Linear Logic (cut elimination proof)
* `all2.v`: sequent calculus for propositional _second-order_ Additive Linear Logic (cut elimination proof)
* `nj1.v`: formulas and natural deduction for _first-order_ Intuitionistic Logic (normalization proof)
* `nj2.v`: formulas and natural deduction for propositional _second-order_ Intuitionistic Logic


* `hilbert.v`: Hilbert system for _first-order_ Intuitionistic Logic (standard alpha-equivalence-free presentation)
* `hilbert2nj.v`: translation of Hilbert system into natural deduction
* `nj2hilbert.v`: translation of natural deduction into hilbert system

Variations:

* `*_ar.v`: terms with arity checks
* `*_vec.v`: terms with vector arguments to control arities

With **cut-elimination/normalization** proofs as main results.

The presentation is shown to be equivalent with Hilbert system as far as provability is concerned.

Current examples are developed in Coq, but formalization does not depend on the surrounding meta-theory and should be adaptable to (any?) proof assistant.

