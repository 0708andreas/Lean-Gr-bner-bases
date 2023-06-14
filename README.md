# Gröbner bases in Lean3

This is the result of a 10 ECTS points project done at Aarhus University, to implement a non-trivial part of mathematics in Lean3. The code consists of the following parts:

- dickson.lean + dickson_add_monoid: a proof of Dicksons lemma
- monomial_order.lean: Formalization of monomial orders and basic lemmas about them
- initial_term.lean: Formalization of the initial term of a multivariate polynomial as well as results on their behaviour
- mv_division.lean: Implementation of the multivariate division algorithm
- grobner_bases.lean: Definition of Gröbner bases and a proof that every ideal has a Gröbner basis.

## Project repport
Apart from the code, the primary outcome of this project is a document, aiming at helping other mathematicians getting into Lean. This is found in the `tex` folder. It is not intended as a Lean tutorial, as that is already covered by the Natural Number Game, but rather as a text for intermediaries. It explains the mathematical underpinnings of Lean, and covers a number of topics I found confusing, when doing this project.
