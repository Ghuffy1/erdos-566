# Verification passed

The selected proof commit `ac0b12b5cb264a092ef1cdf6304760dcdc4b6328` gives a complete disproof of Erdős problem 566, corresponding to JSP-000456, under Lean's standard classical foundations. The original source and all required hypotheses are accounted for in [the correspondence review](STATEMENT_CORRESPONDENCE.md).

| Question | Judgment | Evidence |
| --- | --- | --- |
| Does the proof address the original problem? | Yes, under the canonical nondegenerate formulation | Ordinary Ramsey number, all local edge bounds for at least two vertices, fixed G, all target orders, and the positive-degree condition are retained. |
| Did the selected commit pass the executed checks? | Yes | The clean project build, explicit module builds, source checks, axiom audit, and fresh kernel replay all returned zero. |
| Does it fully resolve the original assertion? | Yes, by disproof | The closed theorem constructs the fixed sparse counterexample and proves unbounded ratios along clique targets. |
| Does the formal proof meet the completeness requirement? | Meets | The sampled-cube existence step is proved, every recorded declaration was checked, and only standard axioms occur. |

## Version and traceability

The checked source commit is `ac0b12b5cb264a092ef1cdf6304760dcdc4b6328` on the original prepared repository's main branch. The proof file SHA-256 is `6eead12291efc2353ca685b0cf82d888689a8116175653df6804e7ccc3b49f50`. The selected version includes both `Erdos566` and `Verification` as default build targets. A separate checkout was created directly from this local repository for the run.

The canonical problem statement was checked against Formal Conjectures revision `2f91d251c07fbbaf9435166d47c11e884a08a6cf`. The question's source, the original Ramsey definition, the complete mathematical paper, and the prior ingredients are recorded in [SOURCES.md](../SOURCES.md).

The evidence below certifies this selected proof version. Later commits add the evidence, submission packet, and CI hardening. The mathematical source and its pinned dependencies are compared byte for byte with the checked version by `scripts/check_submission.py`.

## Actual execution

Lean is 4.34.0. Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`, and all nine dependency revisions and tracked trees were checked before and after execution. The checked-in lockfile and source hash manifest were preserved.

| Check | Exit code | Seconds | Evidence |
| --- | --- | --- | --- |
| lake_version | 0 | 0.469 | [log](logs/lake_version.log) |
| lean_version | 0 | 76.469 | [log](logs/lean_version.log) |
| build | 0 | 1082.203 | [log](logs/build.log) |
| explicit_modules | 0 | 214.234 | [log](logs/explicit_modules.log) |
| source_trust_zero | 0 | 299.343 | [log](logs/source_trust_zero.log) |
| independent_statement | 0 | 55.094 | [log](logs/independent_statement.log) |
| axiom_audit | 0 | 20.578 | [log](logs/axiom_audit.log) |
| fresh_kernel_replay | 0 | 1121.578 | [log](logs/fresh_kernel_replay.log) |

The project build output directory was cleared before the recorded build. Cleanup is confined to that directory, and the verified dependency cache is retained. The process-local environment used `LEAN_NUM_THREADS=2`. Source checking used `-DautoImplicit=false -t 0` and one elaboration worker. The run began at `2026-11-11T14:44:08.940210+00:00` and completed at `2026-11-11T15:32:23.343829+00:00`.

The clean build emitted 62 style, unused-variable, and deprecation warnings. They are retained in the build log.

During environment preparation, dependency rebuilds encountered local file-access errors. An earlier final run was interrupted during Windows session shutdown, with exit codes 0x40010004 and 0xC000026B. The successful recorded run used a new checkout and lower process-local parallelism. The proof source and dependency revisions were unchanged.

## Coverage and axioms

All 420 listed theorem declarations were checked. The list contains the 418 declarations in the complete proof and two additional original-statement declarations. The three main targets are

- `Erdos566.original_statement_false`
- `PrizeStatement.original_problem_false`
- `Verification.original_problem_false`

Each main target depends only on `propext`, `Classical.choice`, and `Quot.sound`. The full declaration inventory, exact command arrays, target-specific axiom lists, output hashes, and timings are in [result.json](result.json). The executed source is in [Audit.lean](Audit.lean).

The bridge in `Verification.lean` independently spells out the original problem's objects, quantifiers, and conditions. Its negation is checked against the completed theorem. The fresh replay target is `Verification`, so the replay includes that module, the complete imported proof, and its imported environment.

## Trust and review limits

This is a contributor-run, AI-assisted verification on a dedicated native Windows checkout. It reused a revision-checked dependency cache restored during environment preparation. A separate operating-system sandbox was unavailable. The kernel replay uses Lean's own checker. Independent implementation checking and independent human mathematical review remain pending.

The mathematical paper was reread, its exact rational certificates checked, and all twelve rendered pages inspected. The local build and kernel results support the complete formal disproof. The prize organizers still perform their own mathematical, formal, attribution, identity, and eligibility review.

The GitHub workflow has been checked for YAML and shell syntax and has pinned dependencies. Its hosted execution is a separate check after publication. Personal claims, identity confirmation, public review dates, and awards remain subject to the official process. The literature search is recorded in [LITERATURE_REVIEW.md](../submission/LITERATURE_REVIEW.md), with its search limits and source comparisons.

## Reproduce

Check out the selected commit, obtain the pinned public dependency cache with `lake exe cache get`, and run

```sh
LEAN_NUM_THREADS=2 python3 scripts/verify.py --output-dir ../fresh-erdos566-evidence --expect-commit ac0b12b5cb264a092ef1cdf6304760dcdc4b6328 --fresh-kernel
```

Use a new output directory for each run. The raw logs are preserved in [logs](logs/). The JSON report records paths using `<PROJECT_ROOT>` and `<EVIDENCE>` so it can be published without machine-specific directory details.

## Hosted reproduction

The [public GitHub workflow](https://github.com/Ghuffy1/erdos-566/actions/runs/43050205767) also passed for commit `77ce4b104c0e03b066fa10ae7e24d2099d93c980`. It fetched the pinned dependencies, rebuilt the project, checked both source modules at trust level zero, audited all 420 declarations, and completed fresh kernel replay. The mathematical source and dependency pins match the selected proof commit. The recorded commands and source hashes are in [hosted.json](hosted.json).
