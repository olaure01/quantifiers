# Formalizing Quantifiers

A formalization of quantifiers based on:

* formulas as first-order structures
* binding for quantifier rules implemented with de Bruijn indices

It applies to:

* first-order logics
* second-order propositional logics (a la system F for example)

Examples files:

* `fot.v`: definitions and properties of first-order terms
* `all1.v`: sequent calculus for _first-order_ Additive Linear Logic
* `all2.v`: sequent calculus for _second-order_ propositional Additive Linear Logic
* `nj1.v`: natural deduction for _first-order_ Intuitionistic Logic

With **cut-elimination/normalization** proofs as main result in each case.

Current examples are developed in Coq, but formalization does not depend on the surrounding meta-theory and should be adaptable to (any?) proof assistant.


