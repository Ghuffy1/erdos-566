"""Check the pinned submission and record actual Lean executions.

The output directory must be new and outside the source repository. The script
uses the toolchain selected by Lake and the checked-in dependency lockfile.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_output(*arguments):
    return subprocess.check_output(
        ["git", "-C", str(ROOT), *arguments], text=True, encoding="utf-8"
    ).strip()


def parse_axioms(text, expected):
    results = {}
    pattern = r"'?([\w.]+)'? depends on axioms: \[([^\]]*)\]"
    for name, body in re.findall(pattern, text, re.DOTALL):
        results[name] = sorted({x.strip() for x in body.split(",") if x.strip()})
    for name in re.findall(r"'?([\w.]+)'? does not depend on any axioms", text):
        results[name] = []
    missing = sorted(set(expected) - results.keys())
    if missing:
        raise ValueError("Missing axiom reports for " + ", ".join(missing))
    unexpected = sorted({x for name in expected for x in results[name]} - STANDARD_AXIOMS)
    if unexpected:
        raise ValueError("Additional axiom dependencies " + ", ".join(unexpected))
    return {name: results[name] for name in expected}


def dependency_state():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    results = []
    for package in manifest["packages"]:
        path = ROOT / ".lake" / "packages" / package["name"]
        revision = subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
        ).strip()
        changes = subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
            text=True,
        ).strip()
        if revision != package["rev"] or changes:
            raise ValueError("Dependency revision or tracked tree differs for " + package["name"])
        results.append({"name": package["name"], "revision": revision, "tracked_tree_clean": True})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    parser.add_argument("--expect-commit")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--fetch-cache", action="store_true")
    parser.add_argument("--fresh-kernel", action="store_true")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    if output == ROOT or ROOT in output.parents:
        parser.error("Choose an output directory outside the repository")
    if args.jobs < 1:
        parser.error("The job count must be positive")
    output.mkdir(parents=True, exist_ok=False)
    commit = git_output("rev-parse", "HEAD")
    if args.expect_commit and commit != args.expect_commit:
        raise ValueError("The checkout differs from the requested commit")
    if git_output("status", "--porcelain", "--untracked-files=no"):
        raise ValueError("The tracked source tree must be clean before verification")

    pins = json.loads((ROOT / "verification" / "source-pins.json").read_text(encoding="utf-8"))
    source_hashes = {name: digest(ROOT / name) for name in pins["files"]}
    if source_hashes != pins["files"]:
        raise ValueError("A pinned proof, manuscript, or dependency file differs")

    names = (ROOT / "verification" / "declarations.txt").read_text(encoding="utf-8").splitlines()
    if len(names) != 420 or len(set(names)) != len(names):
        raise ValueError("The declaration inventory must contain exactly 420 unique names")
    audit = output / "Audit.lean"
    audit.write_text(
        "import Verification\n\n"
        "#print Erdos566.OriginalStatement\n"
        "#print PrizeStatement.Statement\n"
        "#print Verification.originalProblem\n"
        "#print Erdos566.original_statement_false\n"
        "#print PrizeStatement.original_problem_false\n"
        "#print Verification.original_problem_false\n"
        + "\n".join("#check @" + name + "\n#print axioms " + name for name in names)
        + "\n",
        encoding="utf-8",
    )

    environment = os.environ.copy()
    environment.pop("LEAN_PATH", None)
    environment.pop("LEAN_SRC_PATH", None)
    runs = []
    record = {
        "schema_version": 1,
        "checked_commit": commit,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "source_hashes": source_hashes,
        "declaration_count": len(names),
        "runs": runs,
        "execution_environment": "Local host with a dedicated checkout and pinned dependency cache",
        "operating_system_sandbox": False,
        "independent_checker_implementation": False,
        "status": "running",
    }

    def save():
        (output / "result.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")

    def run(name, arguments, timeout=3600):
        command = [args.lake, *arguments]
        log = output / (name + ".log")
        started = time.monotonic()
        print(json.dumps({"started": name}), flush=True)
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(
                command, cwd=ROOT, env=environment, stdout=stream,
                stderr=subprocess.STDOUT, timeout=timeout,
            )
        entry = {
            "name": name,
            "command": ["lake", *[str(x).replace(str(output), "<EVIDENCE>") for x in arguments]],
            "cwd": "<PROJECT_ROOT>",
            "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "log": log.name,
            "log_sha256": digest(log),
        }
        runs.append(entry)
        save()
        print(json.dumps(entry), flush=True)
        if result.returncode:
            raise RuntimeError(name + " failed, see " + log.name)

    save()
    try:
        run("lake_version", ["--version"])
        run("lean_version", ["env", "lean", "--version"])
        version_output = (output / "lean_version.log").read_text(encoding="utf-8")
        if "version 4.34.0" not in version_output:
            raise ValueError("The selected Lean executable does not match Lean 4.34.0")
        if args.fetch_cache:
            run("dependency_cache", ["exe", "cache", "get"])
        record["dependencies_before"] = dependency_state()
        build_directory = ROOT / ".lake" / "build"
        if build_directory.is_symlink() or not build_directory.resolve().is_relative_to(ROOT):
            raise ValueError("The project build directory must stay inside this checkout")
        existed = build_directory.exists()
        if existed:
            shutil.rmtree(build_directory)
        record["project_build_cleanup"] = {
            "directory": ".lake/build",
            "existed": existed,
            "removed": existed,
            "dependency_cache_preserved": True,
        }
        save()
        run("build", ["build"])
        run("explicit_modules", ["build", "+Erdos566", "+Verification"])
        common = ["env", "lean", "-j", str(args.jobs), "-DautoImplicit=false", "-t", "0"]
        run("source_trust_zero", [*common, "Erdos566.lean"])
        run("independent_statement", [*common, "Verification.lean"])
        run("axiom_audit", [*common, str(audit)])
        record["axioms"] = parse_axioms((output / "axiom_audit.log").read_text(encoding="utf-8"), names)
        if args.fresh_kernel:
            run("fresh_kernel_replay", ["env", "leanchecker", "--fresh", "--verbose", "Verification"])
        record["fresh_kernel_replay"] = args.fresh_kernel
        record["dependencies_after"] = dependency_state()
        if record["dependencies_before"] != record["dependencies_after"]:
            raise ValueError("Dependency state changed during verification")
        if git_output("rev-parse", "HEAD") != commit:
            raise ValueError("The selected commit changed during verification")
        if git_output("status", "--porcelain", "--untracked-files=no"):
            raise ValueError("The tracked tree changed during verification")
        if any(digest(ROOT / name) != expected for name, expected in source_hashes.items()):
            raise ValueError("Pinned source changed during verification")
        record["status"] = "passed"
        record["standard_axioms_only"] = True
    except Exception as error:
        record["status"] = "failed"
        record["error"] = str(error)
        raise
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    print(json.dumps({"status": "passed", "commit": commit, "declarations": len(names)}), flush=True)


if __name__ == "__main__":
    main()
