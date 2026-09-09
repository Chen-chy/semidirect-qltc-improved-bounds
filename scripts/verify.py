#!/usr/bin/env python3
"""Run finite and repository checks, never an asymptotic/Lean theorem audit."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "verification/baseline"


def digest_files(directory: Path) -> dict[str, str]:
    return {p.relative_to(directory).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(directory.rglob("*")) if p.is_file()}


def main() -> int:
    if not __debug__ or sys.flags.optimize:
        print("Refusing optimized Python: assertions are part of the finite checks.", file=sys.stderr)
        return 2
    if sys.version_info < (3, 10):
        print("Python 3.10 or later is required", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(".artifacts/verification"))
    args = parser.parse_args()
    output = (ROOT / args.output).resolve() if not args.output.is_absolute() else args.output.resolve()
    # Never allow an output path to overwrite source baselines or historical evidence.
    permitted = [(ROOT / ".artifacts").resolve(), (ROOT / "verification/packaging_run").resolve()]
    if not any(output.is_relative_to(path) for path in permitted):
        print("Output must be inside .artifacts/ or verification/packaging_run/", file=sys.stderr)
        return 2
    output.mkdir(parents=True, exist_ok=True)
    before = digest_files(BASELINE)
    report = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(), "platform": platform.system(),
        "scope": "repository checks and finite structural experiments only",
        "lean_kernel": "NOT_RUN", "lean_full_existence": "NOT_PROVED",
        "asymptotic_theorem_machine_verified": False,
        "github_actions_execution": "NOT_RUN_BY_THIS_COMMAND",
        "steps": [], "baseline_comparisons": {}, "errors": [],
    }
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    # Keep assertions enabled in child interpreters as well.
    env.pop("PYTHONOPTIMIZE", None)

    def run(name: str, arguments: list[str], timeout: int = 180) -> bool:
        start = time.perf_counter()
        command = [sys.executable, *arguments]
        try:
            proc = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                  encoding="utf-8", errors="replace",
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=timeout, check=False)
            text, code, ran = proc.stdout, proc.returncode, True
        except (OSError, subprocess.TimeoutExpired) as exc:
            text, code, ran = str(exc) + "\n", 1, not isinstance(exc, OSError)
        # Normalize only this checkout's path in retained diagnostics.
        text = text.replace(str(ROOT), "<repository-root>")
        (output / f"{name}.log").write_text(text, encoding="utf-8")
        entry = {"name": name, "command": ["python", *arguments],
                 "returncode": code, "ran": ran,
                 "seconds": round(time.perf_counter() - start, 6), "log": f"{name}.log"}
        entry["command"] = [arg.replace(str(ROOT) + os.sep, "") for arg in entry["command"]]
        if name == "unit_tests":
            match = re.search(r"Ran (\d+) tests? in", text)
            if match:
                entry["tests_run"] = int(match.group(1))
            if not match or int(match.group(1)) == 0:
                entry["returncode"] = code = 1
                report["errors"].append("Test discovery did not report any executed tests")
        report["steps"].append(entry)
        print(f"{name}: {'PASS' if code == 0 else 'FAIL'}", flush=True)
        if code:
            print(text, file=sys.stderr)
            report["errors"].append(f"{name} failed with exit code {code}")
        return code == 0

    ok = run("repository", ["scripts/check_repository.py"])
    if ok:
        ok = run("unit_tests", ["-m", "unittest", "discover", "-s", "tests", "-v"])
    if ok:
        for name, script in [
            ("geometry", "experiments/semidirect_sanity.py"),
            ("chains", "experiments/check_t4_chains.py"),
            ("parameters", "experiments/check_parameters.py"),
        ]:
            target = output / f"{name}.json"
            if target.exists():
                target.unlink()  # A stale successful output cannot satisfy a new run.
            passed = run(name, [script, "--output", str(target)])
            ok = ok and passed
            if passed:
                try:
                    actual = json.loads(target.read_text(encoding="utf-8"))
                    expected = json.loads((BASELINE / f"{name}.json").read_text(encoding="utf-8"))
                    if name == "chains":
                        actual.pop("seconds", None)
                    match = actual == expected
                    report["baseline_comparisons"][name] = "PASS" if match else "FAIL"
                    if not match:
                        ok = False
                        report["errors"].append(f"{name}: exact baseline mismatch")
                except (OSError, ValueError) as exc:
                    ok = False
                    report["errors"].append(f"{name}: missing or invalid output: {exc}")
    report["baselines_unchanged"] = before == digest_files(BASELINE)
    if not report["baselines_unchanged"]:
        ok = False
        report["errors"].append("Read-only baseline files changed")
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    report["result"] = "PASS_FINITE_AND_REPOSITORY_CHECKS_ONLY" if ok else "FAIL"
    report["exit_code"] = 0 if ok else 1
    (output / "summary.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n",
                                         encoding="utf-8")
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return report["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
