# Formalizing Quantifiers

(working with `Coq 8.10.2`)

A formalization of quantifiers based on:

* formulas as first-order structures (no alpha-equivalence)
* binding for quantifier rules implemented with de Bruijn indices

Content:

* `stdlib_more.v`: various lemmas missing in the standard library
* `dectype.v`: types (including infinite ones) with Boolean equality

* `term_tactics.v`: some tactics used in following files
* `foterms.v`: definitions and properties of first-order terms (with two kinds of variables)
* `foformulas.v`: definitions and properties of first-order formulas

* `nj1_frl.v`: natural deduction for _first-order_ Intuitionistic Logic with universal quantification only (normalization proof)

Current examples are developed in Coq, but formalization does not depend on the surrounding meta-theory and should be adaptable to (any?) proof assistant.

*(Thanks to Damien Pous for important suggestions and support.)*