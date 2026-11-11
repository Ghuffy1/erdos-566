# Submission readiness and rules review

The governing snapshot is `TheJustinSunPrize/awards` commit `b1bfe454d37db2838ef76756830aeb23c40de95e`, reviewed on November 11, 2026. The source-file hashes are recorded in rules-snapshot.json.

## Prepared materials

| Requirement | Evidence in this preparation |
| --- | --- |
| Correct problem and route | JSP-000456 is the current entry for Erdős 566. The entry is outside the MathDB pilot and follows the legacy route. |
| Complete mathematical solution | `paper/paper.pdf`, Theorem 1.1, Sections 2–7, and Appendix A. |
| Complete formal proof | `Erdos566.lean`, including the unconditional original-statement disproof. |
| Exact statement correspondence | `Verification.lean`, `verification/STATEMENT_CORRESPONDENCE.md`, and `verification/targets.json`. |
| Original source and fixed revision | Original problem and canonical statement sources are given in SOURCES.md. The selected proof commit is recorded in metadata.json and is retained on main. |
| Reproducible dependencies and checks | Exact Lean version, complete Lake lockfile, source hashes, verification script, default module targets, and pinned CI workflow. |
| Actual checking evidence | The final verification report and full raw logs identify the executed commit, checks, exit codes, trust dependencies, and remaining external checks. |
| Proper primary submitter | Ghuffy1 is the designated owner and primary submitter. The intended repository is Ghuffy1/erdos-566. |
| Equal contributor attribution | AUTHORS.md and formalization.yaml name all four contributors, with equal mathematical and formalization credit. |
| Source credits and licenses | SOURCES.md, NOTICE, LICENSE, LICENSE-OpenAI, and paper/LICENSE retain attribution and clarify the licensing scope. |
| AI disclosure | The manuscript acknowledgment, source notes, AUTHORS.md, and formalization.yaml disclose AI assistance. |
| Joint PR template | PR_BODY.md supplies the combined-submission fields, proof links, theorem names, original statement, scope, reproduction, attribution, and review limits. |
| Allowed catalog change | catalog.patch changes only the selected catalog entry's status, contributor/proof information, attribution basis, and publication details. |
| Source files hosted in original repository | The proposed awards patch contains a catalog edit. The proof, manuscript, and build materials stay in this repository. |
| Duplicate review | RELATED_SUBMISSIONS.md documents the located PRs and the observed scope of their source. |
| Individual claims | Four claim drafts name the respective applicants and retain the required personal declarations for completion by those applicants. |
| Identity correspondence | Individual unsent email drafts are kept outside the publication repository. The public materials describe the verification method without private identity documents. |
| Privacy | This preparation has stayed local. Identity documents, payment information, private correspondence, and machine-specific verification paths are excluded from the publication files. |

## Future external steps

The following items require the owner's authorized release, personal participation, or an organizer decision.

| Step | Present state |
| --- | --- |
| Publish the repository and resolve public proof links | Pending owner authorization. The proposed URL is explicitly recorded as a planned destination. |
| Confirm each contributor's role and account connection | Personal confirmation pending. Public account existence has been checked. |
| Confirm personal-repository coauthor Lean claims | Pending organizer interpretation. The joint source is owned by Ghuffy1, and the rules expressly describe applicant-owned and organization repositories. Each coauthor's draft calls out the shared personal-repository source. |
| Establish independent public completion history | Pending public release. Private Git timestamps alone establish no priority. |
| Submit the joint proof PR | Pending owner authorization and publication. |
| Complete organizer mathematical review | Pending submission and review. |
| Complete organizer formal verification | Pending submission and review. |
| Reconcile catalog index and eligibility fields | A maintainer responsibility after review. The proposed external patch preserves those fields. |
| Supply a merged contribution PR in each claim | Pending the actual merge. Drafts explicitly retain this prerequisite. |
| File individual claims and send identity emails | Each applicant acts personally from their own account and address. |
| Establish public-notice dates | The organizer starts a separate 14-day review for each accepted role. |
| Resolve challenges and confirm recipients | Pending organizer review and personal confirmation. |
| Determine awards and payment arrangements | Pending the official process. Equal contribution credit has been recorded without inventing a monetary allocation. |

## Rules references

- [Submission requirements](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/CONTRIBUTING.md)
- [Legacy process](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/award-process.md)
- [Attribution and identity](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/attribution.md)
- [Verification](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/verification.md)
- [PR template](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/.github/PULL_REQUEST_TEMPLATE.md)
- [Individual claim form](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/.github/ISSUE_TEMPLATE/claim-award.yml)

The project permits alternative pre-submission verification methods. The supplied checks use a dedicated local checkout and native Lean execution. A separate operating-system sandbox and an independently implemented proof checker are outside the completed checks and are disclosed in the verification report.
