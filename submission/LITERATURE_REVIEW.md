# Literature and public-source review

The final search was refreshed on November 11, 2026 before submission. It found no earlier complete resolution of the same ordinary-Ramsey assertion in the sources examined. Priority remains subject to further evidence and the prize organizers' review.

## Scope and method

The searches covered the exact Erdős and JSP identifiers, “Ramsey size linear”, “Ramsey size-linear”, the local edge condition, sparse-graph counterexamples, and the original paper's title. The review used arXiv records and full-text theorem statements, authors' publication pages, the original problem sources, public GitHub code and repository searches, the current prize catalog, and open, merged, and closed prize PRs. References in the related papers supplied additional leads.

The GitHub code queries `Erdos566`, `ramseySizeLinear`, and `"JSP-000456"` returned 38, 144, and 3 records respectively in the recorded refresh. The second query was paginated with capacity for 1,000 results. Search indexing, private research, unavailable pages, and later updates limit every negative search result.

## Original question and related publications

- Erdős, Faudree, Rousseau, and Schelp posed the local-sparsity question in *Ramsey size linear graphs* (1993), Question 1, page 398. The assertion concerns the ordinary Ramsey number and a constant depending on the fixed graph. The original source and the independent formal statement agree on this scope. [Publication](https://doi.org/10.1017/S096354830000078X), [original problem collection](https://mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/SizeRamseyLinear.html).
- Balister, Schelp, and Simonovits prove that adding a sufficiently long path between two vertices preserves size-linearity. Their concluding questions ask about a path of length two and a single subdivision of an edge of the complete graph on four vertices. [Paper, 2002](https://www.renyi.hu/~miki/SimBalis.pdf).
- Bradač, Gishboliner, and Sudakov prove size-linearity for subdivisions of the complete graph on four vertices with at least six vertices, along with further fixed-graph Ramsey bounds. Their concluding questions include the five-vertex subdivision and degenerate-graph estimates. These results supply important surrounding context. [Paper, revised March 10, 2023](https://arxiv.org/abs/2202.10388v2).
- Wigderson proves the existence of infinitely many minimally non-Ramsey-size-linear graphs. The argument uses high-girth graphs of average degree at least four and then takes a minimal obstruction. It supplies an existence theorem for Erdős problem 79. Identifying an obstruction satisfying every local edge bound in problem 566 requires additional information. [Paper, revised May 5, 2025](https://arxiv.org/abs/2409.05931v2).
- Hng, Ji, and Lamaison establish bounds for odd cycles, cliques, and multicolor variants. Their stated results address those specified forbidden graphs and parameters. [Paper, revised March 30, 2026](https://arxiv.org/abs/2603.25453v2).
- Ji studies Ramsey numbers with complete bipartite hosts. The density obstruction in Corollary 1 assumes at least twice as many edges as vertices minus two. The introduction leaves an intermediate density range open. [Paper, revised April 28, 2026](https://arxiv.org/abs/2604.20668v3).
- Barría's September preprint claims size-linearity for graphs with no complete-four-vertex minor. His October preprint treats specified sparse graphs against bipartite targets. His November 3 preprint improves clique-target bounds for a list of small graphs. Their stated scopes leave the general local-sparsity question open. These are preprints, and their correctness is outside the present proof's dependencies. [September manuscript](https://www.preprints.org/manuscript/202609.2254), [October manuscript](https://www.preprints.org/manuscript/202610.0183), [November manuscript](https://www.preprints.org/manuscript/202611.0216).
- OpenAI's Chapter 10 constructs a fixed bipartite two-degenerate graph with a large extremal number. Its layered graph and entropy argument are prior ingredients used here. The present proposed synthesis adds the Ramsey witness, retuned scalar bounds, spectral estimates, and independent-set counting. The manuscript and source retain explicit credit. [Chapter 10](https://cdn.openai.com/pdf/ten-proofs-oai.pdf).

## Public formalizations and submissions

The current Formal Conjectures statement at revision `da703a5f239f734a47ede2f4e99b9ccc9e644cb5` has exactly the same file hash as the earlier statement revision used in the correspondence check. It contains the open question with an unfilled proof. [Canonical statement](https://github.com/google-deepmind/formal-conjectures/blob/da703a5f239f734a47ede2f4e99b9ccc9e644cb5/FormalConjectures/ErdosProblems/566.lean).

The directly inspected `daedalus/alphaproof-nexus` problem file contains imports and an empty development block. The inspected `rjwalters/lean-genius` source contains graph definitions and a constant placeholder for its Ramsey quantity. Its metadata explicitly records that scope. Neither file supplies a theorem resolving the original assertion. [Development file](https://github.com/daedalus/alphaproof-nexus/blob/4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c/problems/erdos/566/Erdos566.lean), [source and metadata](https://github.com/rjwalters/lean-genius/blob/d8540c5a48f69a9f57b87c549c6e09dad63a0670/src/data/proofs/erdos-566/meta.json).

The prize search found two closed, unmerged submissions under the current identifier and a historical numbering record. Their exact source scopes are recorded in [RELATED_SUBMISSIONS.md](RELATED_SUBMISSIONS.md). The current upstream catalog continues to record the question as open at the reviewed rules revision.

## Priority conclusion

The searched records support submitting this complete disproof for mathematical, formal, and attribution review. They establish no exhaustive firstness certificate. Public release supplies a dated version for comparison with any earlier complete proof that may subsequently be identified.
