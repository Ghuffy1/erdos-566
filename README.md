# A locally sparse graph with superlinear Ramsey growth

This repository contains a complete mathematical disproof of Erdős problem 566 and its Lean formalization. The corresponding Justin Sun Prize entry is JSP-000456.

The fixed bipartite graph satisfies every local edge bound in the question. For all sufficiently large positive integers m, the proof gives

\[
R(G,K_{2^{570m}})>2^{1144m-1}.
\]

The ratio to the clique's edge count consequently tends to infinity.

## Authors and ownership

Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer receive equal contribution credit. Ghuffy1 is the designated repository owner and primary submission contact. See [AUTHORS.md](AUTHORS.md) for the account mapping, contribution statement, and AI disclosure.

The public source repository is [Ghuffy1/erdos-566](https://github.com/Ghuffy1/erdos-566). The joint prize submission is [JSP PR #5565](https://github.com/TheJustinSunPrize/awards/pull/5565). Organizer review is pending.

## Mathematical paper

Read [the complete paper](paper/paper.pdf). Its [source](paper/paper.tex) is included. Theorem 1.1 states the result. Sections 2 through 7 prove it, and Appendix A gives exact rational certificates for the numerical estimates. The paper contains the mathematical exposition and bibliography.

## Formal proof

- [Erdos566.lean](Erdos566.lean) contains the complete argument.
- `Erdos566.original_statement_false` is the main unconditional theorem.
- `PrizeStatement.original_problem_false` gives the original formulation.
- [Verification.lean](Verification.lean) independently spells out the problem's definitions and quantifiers and proves `Verification.original_problem_false`.

The two modules are default build targets. The formal argument uses ordinary complete-host Ramsey numbers, a fixed forbidden graph, and target graphs without isolated vertices.

## Reproduce

Install Elan and Python 3.9 or later. The project selects Lean 4.34.0 and fixes every dependency in [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
LEAN_NUM_THREADS=2 python3 scripts/verify.py --output-dir ../erdos-566-verification --fresh-kernel
```

In Windows PowerShell, use

```powershell
lake exe cache get
$env:LEAN_NUM_THREADS = "2"
python .\scripts\verify.py --output-dir ..\erdos-566-verification --fresh-kernel
```

Use a new output directory for each run. The process-local thread setting bounds build parallelism. The verifier checks the exact source hashes and dependency revisions, performs a clean build, checks both modules explicitly, checks the source at trust level zero, audits all 420 theorem declarations, and replays the complete imported environment through Lean's fresh kernel. It writes actual commands, exit codes, timings, and full logs to the selected evidence directory.

Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. The fresh replay uses Lean's own kernel. The verification report identifies the completed checks and their limits.

The full [hosted verification](https://github.com/Ghuffy1/erdos-566/actions/runs/43050205767) passed for the published repository.

## Submission materials

The [submission directory](submission/) contains the joint submission and the proposed catalog-only change. Claim drafts are individual documents because JSP requires each applicant to act through their own account. The [release checklist](submission/RELEASE_CHECKLIST.md) records the publication and review sequence.

The current rules snapshot is Justin Sun Prize revision `b1bfe454d37db2838ef76756830aeb23c40de95e`. Mathematical review, formal verification by the organizers, attribution review, personal identity confirmation, public review, and award decisions belong to the prize process. The local evidence supports that review.

## Sources and licensing

See [SOURCES.md](SOURCES.md) and [NOTICE](NOTICE) for the original problem, prior mathematical ingredients, reused source attribution, and licenses. Source code and verification scripts use Apache License 2.0. The paper's copyright is retained by its authors, as stated in [paper/LICENSE](paper/LICENSE).
