# Formalizing Quantifiers

(working with `Coq 8.12.0`)

A formalization of quantifiers based on:

* formulas as first-order structures (no alpha-equivalence);
* binding for quantifier rules implemented with de Bruijn indices.

### Compiling

        $ ./configure
        $ make

### Content:

* `ollibs/*.v`: external library files from [OLlibs](https://github.com/olaure01/ollibs) (put here to get a self-contained set of files)

* `term_tactics.v`: some tactics used in following files
* `foterms.v`: definitions and properties of first-order terms (with two kinds of variables)
* `foformulas.v`: definitions and properties of first-order formulas
* `nj1.v`: natural deduction for first-order Intuitionistic Logic with universal quantification only (normalization proof)

* `foterms_ext.v`: additional properties of first-order terms
* `foformulas_ext.v`: additional properties of first-order formulas
* `nj1_frlexs.v`: natural deduction for first-order Intuitionistic Logic with both universal and existential quantification (normalization proof and sub-formula property)

* `foterms_std.v`: standard first-order terms (with one kind of variables)
* `hilbert.v`: Hilbert system for first-order Intuitionistic Logic with both universal and existential quantification (standard alpha-equivalence-free presentation)
* `hilbert2nj.v`: translation of Hilbert system into natural deduction
* `nj2hilbert.v`: translation of natural deduction into Hilbert system
* `nj_vs_hilbert.v`: equivalence of the two systems through the previous translations

* `statements.md`: correspondence between statements in the article and in the formalization files

Current examples are developed in Coq, but formalization does not depend on the surrounding meta-theory and should be adaptable to (any?) proof assistant.
