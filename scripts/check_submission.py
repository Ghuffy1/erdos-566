"""Validate the prepared submission's files, ownership metadata, and pinned links."""

import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PRIVATE_PATH = re.compile(r"(?<![A-Za-z])[A-Z]:[\\/]|/(?:Users|home)/[\w-]", re.IGNORECASE)


def main():
    required = [
        "README.md", "AUTHORS.md", "SOURCES.md", "NOTICE", "LICENSE", "LICENSE-OpenAI",
        "Erdos566.lean", "Verification.lean", "lean-toolchain", "lakefile.toml",
        "lake-manifest.json", "CITATION.cff", "formalization.yaml",
        "paper/paper.pdf", "paper/paper.tex", "paper/LICENSE",
        "verification/source-pins.json", "verification/declarations.txt",
        "verification/targets.json", "verification/STATEMENT_CORRESPONDENCE.md",
        "verification/REPORT.md", "verification/result.json",
        "submission/metadata.json", "submission/PR_BODY.md", "submission/catalog.patch",
        "submission/RULES_COMPLIANCE.md", "submission/RELEASE_CHECKLIST.md",
        "submission/RELATED_SUBMISSIONS.md", "submission/rules-snapshot.json",
    ]
    for name in required:
        if not (ROOT / name).is_file():
            raise ValueError("Missing required file " + name)

    metadata = json.loads((ROOT / "submission/metadata.json").read_text(encoding="utf-8"))
    accounts = {"Ghuffy1", "JENW1N", "H0W4RD-dev", "lkruer"}
    if metadata["owner"] != "Ghuffy1" or metadata["primary_submitter"] != "Ghuffy1":
        raise ValueError("Owner or primary submitter differs from the requested account")
    if {p["github"] for p in metadata["contributors"]} != accounts:
        raise ValueError("Contributor list differs from the requested accounts")
    if any(p["mathematical_credit"] != "equal" or p["formalization_credit"] != "equal"
           for p in metadata["contributors"]):
        raise ValueError("The contributor credit must be equal")
    for account in accounts:
        if not (ROOT / "submission/claim-drafts" / (account + ".md")).is_file():
            raise ValueError("Missing individual claim draft " + account)

    proof_commit = metadata["selected_proof_commit"]
    subprocess.run(["git", "merge-base", "--is-ancestor", proof_commit, "HEAD"],
                   cwd=ROOT, check=True)
    pins = json.loads((ROOT / "verification/source-pins.json").read_text(encoding="utf-8"))
    for name, expected in pins["files"].items():
        current = (ROOT / name).read_bytes()
        original = subprocess.check_output(["git", "show", proof_commit + ":" + name], cwd=ROOT)
        if current != original or hashlib.sha256(current).hexdigest() != expected:
            raise ValueError("Pinned content changed for " + name)

    patch = (ROOT / "submission/catalog.patch").read_text(encoding="utf-8")
    headers = re.findall(r"^\+\+\+ (.+)$", patch, re.MULTILINE)
    if headers != ["b/problems/catalog-0401-0500.md"]:
        raise ValueError("The awards patch must affect exactly the intended catalog")
    allowed = ("| Current status |", "| Lean proof |", "| Attribution basis |", "| Publication details |")
    edits = [line[1:] for line in patch.splitlines()
             if line[:1] in {"+", "-"} and not line.startswith(("+++", "---"))]
    if not edits or any(not line.startswith(allowed) for line in edits):
        raise ValueError("The awards patch changes a field outside the allowed contribution fields")
    if "JSP-000456" not in patch:
        raise ValueError("The awards patch must identify JSP-000456")

    checked_links = set()
    link_pattern = r"https://github\.com/Ghuffy1/erdos-566/blob/([0-9a-f]{40})/([^\s)#]+)(?:#L(\d+))?"
    for path in ROOT.rglob("*"):
        if not path.is_file() or ".git" in path.parts or ".lake" in path.parts:
            continue
        if path.suffix.lower() not in {".md", ".json", ".yaml", ".yml", ".txt", ".py", ".lean", ".toml", ".cff", ".log"}:
            continue
        text = path.read_text(encoding="utf-8")
        if PRIVATE_PATH.search(text):
            raise ValueError("Machine-specific path found in " + str(path.relative_to(ROOT)))
        if re.search(r"\b(?:ghp_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|sk-[A-Za-z0-9]{30,})", text):
            raise ValueError("Potential secret found in " + str(path.relative_to(ROOT)))
        for commit, name, line in re.findall(link_pattern, text):
            key = (commit, name, line)
            if key in checked_links:
                continue
            blob = subprocess.check_output(["git", "show", commit + ":" + name], cwd=ROOT)
            if line and int(line) > len(blob.splitlines()):
                raise ValueError("Out-of-range pinned source line " + name)
            checked_links.add(key)

    verification = json.loads((ROOT / "verification/result.json").read_text(encoding="utf-8"))
    if verification["checked_commit"] != proof_commit or verification["status"] != "passed":
        raise ValueError("The proof verification does not match the selected commit")
    if not verification.get("fresh_kernel_replay") or not verification.get("standard_axioms_only"):
        raise ValueError("Fresh replay and the full axiom audit are required in this package")
    for run in verification["runs"]:
        if run["exit_code"] != 0 or Path(run["log"]).name != run["log"]:
            raise ValueError("Invalid verification run " + run["name"])
        log = ROOT / "verification" / "logs" / run["log"]
        if hashlib.sha256(log.read_bytes()).hexdigest() != run["log_sha256"]:
            raise ValueError("Verification log hash differs for " + run["name"])
    print(json.dumps({"status": "passed", "required_files": len(required),
                      "pinned_links_checked": len(checked_links), "proof_commit": proof_commit,
                      "contributors": sorted(accounts)}))


if __name__ == "__main__":
    main()
