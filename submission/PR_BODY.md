## Submission type

- [x] Mathematical solver information
- [x] Lean proof or formalization author information

This is the joint submission for JSP-000456, corresponding to Erdős problem 566. Ghuffy1 is the primary submitter and owner of the original proof repository. All four authors receive equal contribution credit.

## Problem

The original question is [Erdős problem 566](https://www.erdosproblems.com/566), from Erdős, Faudree, Rousseau, and Schelp, *Ramsey size linear graphs* (1993), Question 1 on page 398. The current entry is [JSP-000456](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000456).

The proposed catalog change records a complete disproof, the mathematical authors, the complete Lean proof, and the supporting evidence. It updates only the corresponding detail entry's permitted contribution fields. Maintainers reconcile the index, eligibility, and role-specific claim status after review.

The complete mathematical solution is [A locally sparse graph with superlinear Ramsey growth](https://github.com/Ghuffy1/erdos-566/blob/ac0b12b5cb264a092ef1cdf6304760dcdc4b6328/paper/paper.pdf), dated November 11, 2026. Theorem 1.1 states the result, Sections 2–7 prove it, and Appendix A gives exact scalar bounds.

Related records and the source-level distinctions are described in [RELATED_SUBMISSIONS.md](https://github.com/Ghuffy1/erdos-566/blob/be07da3d31e6a56630bd5c5ccc374ebad627499b/submission/RELATED_SUBMISSIONS.md). PRs 3109 and 2319 are closed and unmerged and contain arithmetic or scoped statements. They do not contain the present complete Ramsey disproof. No external firstness adjudication is claimed.

## Formal statement

The statement and final proof are in [Erdos566.lean](https://github.com/Ghuffy1/erdos-566/blob/ac0b12b5cb264a092ef1cdf6304760dcdc4b6328/Erdos566.lean#L9786). The fully qualified target is `PrizeStatement.original_problem_false`. The independently written statement check is [Verification.lean](https://github.com/Ghuffy1/erdos-566/blob/ac0b12b5cb264a092ef1cdf6304760dcdc4b6328/Verification.lean), with target `Verification.original_problem_false`.

The original statement quantifies over each finite simple graph G satisfying every induced-edge bound for vertex subsets of size at least two. For each fixed G it asks for one positive real constant that bounds the ordinary Ramsey number against every finite H without isolated vertices by that constant times e(H). The proof fixes one bipartite, two-degenerate G and constructs unbounded clique targets violating every such constant. The complete sampled-cube existence argument is included. [The correspondence matrix](https://github.com/Ghuffy1/erdos-566/blob/be07da3d31e6a56630bd5c5ccc374ebad627499b/verification/STATEMENT_CORRESPONDENCE.md) records the hypotheses, quantifiers, definitions, and conclusion.

The canonical formal statement was checked against Formal Conjectures commit `2f91d251c07fbbaf9435166d47c11e884a08a6cf`. We adopt its explicit subgraph-order convention of at least two vertices, where the original prose leaves the lower range implicit. This convention is explained in the correspondence review. Organizer mathematical review is requested and remains pending.

## Proof submission

```json
[
  {
    "repository": "https://github.com/Ghuffy1/erdos-566",
    "branch": "main",
    "commit": "ac0b12b5cb264a092ef1cdf6304760dcdc4b6328"
  }
]
```

The complete proof is in [Erdos566.lean](https://github.com/Ghuffy1/erdos-566/blob/ac0b12b5cb264a092ef1cdf6304760dcdc4b6328/Erdos566.lean), ending with `Erdos566.original_statement_false` and `PrizeStatement.original_problem_false`. The source commit is an ancestor of main. The formal source, paper, and supporting build files belong in the original proof repository. The awards PR contains the catalog edit and links to these materials.

## Reproduction

The project selects Lean `leanprover/lean4:v4.34.0`. Mathlib is pinned at `5ed2965256430c3649e86755f9576b54eca72435`, with all dependencies fixed in [lake-manifest.json](https://github.com/Ghuffy1/erdos-566/blob/ac0b12b5cb264a092ef1cdf6304760dcdc4b6328/lake-manifest.json). The two modules are default targets. [README.md](https://github.com/Ghuffy1/erdos-566/blob/ac0b12b5cb264a092ef1cdf6304760dcdc4b6328/README.md) gives the reproduction instructions.

```sh
git clone https://github.com/Ghuffy1/erdos-566.git
cd erdos-566
git checkout ac0b12b5cb264a092ef1cdf6304760dcdc4b6328
lake exe cache get
LEAN_NUM_THREADS=2 python3 scripts/verify.py --output-dir ../erdos566-evidence --expect-commit ac0b12b5cb264a092ef1cdf6304760dcdc4b6328 --fresh-kernel
```

The verifier performs clean project and explicit module builds, trust-level-zero source checks, original-statement checking, all-declaration axiom checking, and fresh kernel replay. Axiom output for each main target lists only `propext`, `Classical.choice`, and `Quot.sound`. The complete [axiom log](https://github.com/Ghuffy1/erdos-566/blob/be07da3d31e6a56630bd5c5ccc374ebad627499b/verification/logs/axiom_audit.log) supplies the target-specific outputs.

## Pre-submission verification

The [public GitHub workflow](https://github.com/Ghuffy1/erdos-566/actions/runs/43050205767) also passed for commit `77ce4b104c0e03b066fa10ae7e24d2099d93c980`. It fetched the pinned dependencies, rebuilt the project, checked both source modules at trust level zero, audited all 420 declarations, and completed fresh kernel replay. The mathematical source and dependency pins match the selected proof commit. The recorded commands and source hashes are in the workflow's public logs.

Contributor-run verification passed for commit `ac0b12b5cb264a092ef1cdf6304760dcdc4b6328`. The [full report](https://github.com/Ghuffy1/erdos-566/blob/be07da3d31e6a56630bd5c5ccc374ebad627499b/verification/REPORT.md) and [machine-readable record](https://github.com/Ghuffy1/erdos-566/blob/be07da3d31e6a56630bd5c5ccc374ebad627499b/verification/result.json) preserve the actual commands, exit codes, timings, hash checks, and limits.

The method uses native Lean 4.34.0 and its fresh kernel replay. A dedicated checkout was used with revision-checked dependencies. An independently implemented checker and independent human review remain outstanding. Organizer acceptance, attribution, priority, and eligibility are pending.

## Attribution

Will Howe (H0W4RD-dev), Grant Huffman (Ghuffy1), Jensen Kohlmeyer (JENW1N), and Liam Kruer (lkruer) are designated equal contributors to the mathematical solution and formalization. Ghuffy1 is the primary submitter and repository owner. [AUTHORS.md](https://github.com/Ghuffy1/erdos-566/blob/ac0b12b5cb264a092ef1cdf6304760dcdc4b6328/AUTHORS.md) and [formalization.yaml](https://github.com/Ghuffy1/erdos-566/blob/be07da3d31e6a56630bd5c5ccc374ebad627499b/formalization.yaml) record that declaration. Personal confirmations and the organizer's account-to-author checks remain required.

OpenAI's ChatGPT assisted with mathematical development, formalization, verification, exposition, and preparation. The paper and [SOURCES.md](https://github.com/Ghuffy1/erdos-566/blob/ac0b12b5cb264a092ef1cdf6304760dcdc4b6328/SOURCES.md) credit the prior layered graph and entropy framework, the classical independent-set method, and the reused source licenses. No independent human verifier is designated.

The original local preparation history was AI-assisted. Local commit author fields and repository control do not by themselves establish personal identity or firstness. Each contributor's own claim and identity confirmation are handled through the applicable prize process. The shared personal-repository arrangement for individual Lean coauthor claims is disclosed for organizer confirmation.

## Submission checklist for the primary submitter

- [x] The prepared patch changes the permitted contribution fields in the relevant catalog entry.
- [x] The submitted mathematical result resolves the full original assertion by disproof.
- [x] The complete mathematical paper is supplied together with the complete Lean proof.
- [x] The selected proof is complete and its original-statement bridge and standard-axiom audit passed.
- [x] The selected commit is retained on the named branch, and reproduction evidence is supplied.
- [x] The awards patch contains no proof source, archives, binaries, vendored dependencies, or private identity/payment information.
- [x] The primary submitter requested the stated joint attribution and authorized this submission from the Ghuffy1 account. Each applicant will complete the official personal confirmation process for their own claim.
- [x] I have authorized public release and confirmed that all linked public materials resolve at the selected revisions.
