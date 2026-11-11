# Mathematical and source provenance

## Original question

P. Erdős, R. J. Faudree, C. C. Rousseau, and R. H. Schelp, *Ramsey size linear graphs*, Combinatorics, Probability and Computing 2 (1993), 389–399, Question 1 on page 398. The question is recorded as Erdős problem 566 and corresponds to JSP-000456.

- [Original publication](https://doi.org/10.1017/S096354830000078X)
- [Erdős problem 566](https://www.erdosproblems.com/566)
- [JSP entry at the rules snapshot](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/problems/catalog-0401-0500.md#JSP-000456)

The statement is the ordinary Ramsey assertion with an existential constant depending on the fixed graph. The local sparsity condition applies to every vertex set of size at least two. The target graph has no isolated vertices. A single fixed graph with unbounded Ramsey-to-edge-count ratios disproves this assertion.

## Canonical formulation

The definitions and quantifiers were compared with the following Formal Conjectures revision. The independent statement in Verification.lean also specifies the complete-host Ramsey definition directly.

- [Erdős 566 statement](https://github.com/google-deepmind/formal-conjectures/blob/2f91d251c07fbbaf9435166d47c11e884a08a6cf/FormalConjectures/ErdosProblems/566.lean)
- [Ordinary Ramsey definition](https://github.com/google-deepmind/formal-conjectures/blob/2f91d251c07fbbaf9435166d47c11e884a08a6cf/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean)

## Prior ingredients

OpenAI, *Ten advances in mathematics and theoretical computer science*, updated August 6, 2026, Chapter 10, Theorem 1.2 on page 237 and Sections 5–8 on pages 242–248, supplies the prior layered construction, entropy-potential framework, and child-array counting ingredients.

- [Mathematical source](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Associated source repository](https://github.com/openai/ten-proofs)

The reused source is `CompactnessAndDegeneracy.lean`, Git blob `0e973d50014e8c800af597ef699ef29b81e42fc6`, under Apache License 2.0. The adaptation adds the local sparsity argument and the one-cube Ramsey construction, retunes the entropy inequality, and establishes the spectral and independent-set estimates needed for the disproof. The original upstream license is retained in LICENSE-OpenAI.

The maximum-degree independent-set encoding is the classical Kleitman–Winston method. A source for this method is J. Balogh, A. Treglown, and A. Z. Wagner, *Applications of graph containers in the Boolean lattice*, Random Structures and Algorithms 49 (2016), 845–872, Section 3.

- [Published article](https://doi.org/10.1002/rsa.20666)

The manuscript proves the entropy, counting, spectral, and probabilistic estimates it uses. The formal source proves their counterparts against the pinned Mathlib dependencies.
