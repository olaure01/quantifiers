# Formalizing Quantifiers

(working with `Coq 8.14.1` and [`OLlibs 2.0.2`](https://github.com/olaure01/ollibs))

A formalization of quantifiers based on:

* formulas as first-order structures (no alpha-equivalence);
* binding for quantifier rules implemented with de Bruijn indices.

It applies to:

* first-order logics;
* propositional second-order logics (a la system F for example).

### Installation

Requires [OLlibs](https://github.com/olaure01/ollibs) (add-ons for the standard library): [see installation instructions](https://github.com/olaure01/ollibs/blob/master/README.md).

1. [install OLlibs](https://github.com/olaure01/ollibs/blob/master/README.md)
2. install development

        $ ./configure
        $ make
        $ make install

### Content:

* `term_tactics.v`: some tactics used in following files
* `foterms.v`: definitions and properties of first-order terms (with two kinds of variables)
* `foterms_ext.v`: additional properties of first-order terms
* `foterms_std.v`: standard first-order terms (with one kind of variables)
* `foformulas.v`: definitions and properties of first-order formulas
* `foformulas_ext.v`: additional properties of first-order formulas

* `nj1_frl.v`: natural deduction for _first-order_ Intuitionistic Logic with universal quantification only (normalization proof)
* `nj1.v`: natural deduction for _first-order_ Intuitionistic Logic (normalization proof and sub-formula property)
* `all1.v`: sequent calculus for _first-order_ Additive Linear Logic (cut elimination proof)
* `all2.v`: sequent calculus for propositional _second-order_ Additive Linear Logic (cut elimination proof)
* `F.v`: formulas and natural deduction for propositional _second-order_ Intuitionistic Logic (universal quantification only, i.e. System F)
* `nj2.v`: formulas and natural deduction for propositional _second-order_ Intuitionistic Logic

* `hilbert.v`: Hilbert system for _first-order_ Intuitionistic Logic with both universal and existential quantifications (standard alpha-equivalence-free presentation)
* `hilbert2nj.v`: translation of Hilbert system into natural deduction
* `nj2hilbert.v`: translation of natural deduction into Hilbert system
* `nj_vs_hilbert.v`: equivalence of the two systems through the previous translations

Variations:

* `*_ar.v`: terms with arity checks
* `*_vec.v`: terms with vector arguments to control arities


Current examples are developed in Coq, but formalization does not depend on the surrounding meta-theory and should be adaptable to (any?) proof assistant.

*(Thanks to Damien Pous for important suggestions and support.)*
