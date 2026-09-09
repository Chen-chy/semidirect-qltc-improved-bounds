#!/usr/bin/env python3
"""Fail-closed Lean compilation, public-theorem axiom audit, and scope audit.

The default `full` scope does not succeed merely because a conditional theorem
compiles. `modules` checks the modular development without claiming a closed
existence theorem. All result files describe what was actually run.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FULL_THEOREM = "SemidirectQLTC.T4.exists_logSquareSemidirectFamily"
BANNED = re.compile(
    r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b"
    r"|debug\.skipKernelTC"
)


def lean_code(text: str) -> str:
    """Erase Lean comments and strings while retaining newlines for diagnostics."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        c = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if c == "\n" else " "); i += 1
        elif in_string:
            if c == "\\" and i + 1 < len(text):
                out.extend("  "); i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                if c == '"': in_string = False
                i += 1
        elif text.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0: j = len(text)
            out.extend(" " * (j-i)); i = j
        elif c == '"':
            in_string = True; out.append(" "); i += 1
        else:
            out.append(c); i += 1
    if depth or in_string:
        raise ValueError("Unterminated comment or string in Lean source")
    return "".join(out)


def inventory() -> tuple[list[dict], list[dict], dict[str, str]]:
    declarations: list[dict] = []
    violations: list[dict] = []
    hashes: dict[str, str] = {}
    paths = [ROOT / "T4.lean"]
    paths += sorted((ROOT / "T4").glob("*.lean"))
    paths += sorted((ROOT / "SemidirectQLTC").glob("*.lean"))
    for path in paths:
        rel = str(path.relative_to(ROOT))
        raw = path.read_bytes()
        hashes[rel] = hashlib.sha256(raw).hexdigest()
        text = lean_code(raw.decode("utf-8"))
        for match in BANNED.finditer(text):
            violations.append({"file": rel, "line": text.count("\n", 0, match.start()) + 1,
                               "token": match.group(0)})
        namespaces: list[str] = []
        for lineno, line in enumerate(text.splitlines(), 1):
            ns = re.match(r"\s*namespace\s+([\w.]+)", line)
            if ns:
                namespaces.append(ns.group(1)); continue
            end = re.match(r"\s*end\s+([\w.]+)", line)
            if end and namespaces and end.group(1) == namespaces[-1]:
                namespaces.pop(); continue
            decl = re.search(r"\b(theorem|lemma)\s+([\w']+)\b", line)
            if decl and not re.search(r"\bprivate\b", line[:decl.start()]):
                name = ".".join(namespaces + [decl.group(2)])
                declarations.append({"name": name, "file": rel, "line": lineno})
    names = [d["name"] for d in declarations]
    if len(names) != len(set(names)):
        raise ValueError("Duplicate declaration names in the audit inventory")
    return declarations, violations, hashes


def write_json(name: str, data: object) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def run(command: list[str], logname: str, timeout: int = 1800) -> dict:
    record: dict = {"command": command, "cwd": str(ROOT)}
    try:
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=timeout, check=False)
        output = result.stdout
        record.update(returncode=result.returncode, ran=True)
    except FileNotFoundError as exc:
        output = f"Command could not start: {exc}\n"
        record.update(returncode=127, ran=False, error="EXECUTABLE_NOT_FOUND")
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes): output = output.decode("utf-8", errors="replace")
        output += "\nValidation command timed out. No passing result is inferred.\n"
        record.update(returncode=124, ran=True, error="TIMEOUT")
    (OUT / logname).write_text(output, encoding="utf-8")
    record["log"] = f"verification/{logname}"
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope", choices=("full", "modules"), default="full")
    parser.add_argument("--lake", default="lake", help="Lake executable or full path")
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    declarations, violations, hashes = inventory()
    write_json("declarations.json", declarations)
    write_json("source_hashes.json", hashes)
    write_json("source_scan.json", {"status": "FAIL" if violations else "PASS",
        "meaning": "Lexical screen only; NOT Lean elaboration or kernel checking",
        "violations": violations, "public_theorems": len(declarations)})
    obligations = json.loads((ROOT / "docs/obligations.json").read_text(encoding="utf-8"))
    open_obligations = [o["id"] for o in obligations if o["status"] != "CLOSED"]
    status: dict = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "requested_scope": args.scope,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "source_scan": "FAIL" if violations else "PASS",
        "kernel_status": "NOT_RUN", "axiom_audit_status": "NOT_RUN",
        "full_t4_existence_theorem": "NOT_PROVED",
        "full_theorem_name_required": FULL_THEOREM,
        "full_theorem_present_in_source_inventory": FULL_THEOREM in {d["name"] for d in declarations},
        "open_obligations": open_obligations,
        "public_theorems_in_inventory": len(declarations),
        "lake_found": shutil.which(args.lake),
        "lean_found": shutil.which("lean"),
    }

    def finish(code: int, result: str) -> int:
        status["result"] = result
        status["exit_code"] = code
        write_json("status.json", status)
        print(json.dumps(status, indent=2, ensure_ascii=False))
        return code

    if violations:
        return finish(2, "SOURCE_SCREEN_REJECTED")
    # Attempt the actual requested build. Missing binaries are recorded as NOT_RUN,
    # not as a proof failure and not as a passing validation.
    build = run([args.lake, "build", "T4"], "build.log")
    status["build"] = build
    if build["returncode"]:
        status["kernel_status"] = "NOT_RUN" if not build["ran"] else "BUILD_FAILED"
        return finish(build["returncode"], "BLOCKED_NO_LAKE" if not build["ran"] else "BUILD_FAILED")
    status["kernel_status"] = "MODULE_BUILD_PASS"
    version = run([args.lake, "env", "lean", "--version"], "lean_version.log", timeout=30)
    status["compiler_version_probe"] = version
    if version["returncode"]:
        return finish(3, "COMPILER_VERSION_PROBE_FAILED")
    audit_text = "import T4\n\n" + "\n".join(
        f'#print axioms {d["name"]}' for d in declarations) + "\n"
    (OUT / "Axioms.lean").write_text(audit_text, encoding="utf-8")
    audit = run([args.lake, "env", "lean", "-DwarningAsError=true", "verification/Axioms.lean"],
                "axioms.log")
    status["axiom_audit_command"] = audit
    if audit["returncode"]:
        status["axiom_audit_status"] = "AUDIT_COMMAND_FAILED"
        return finish(3, "AXIOM_AUDIT_FAILED")
    text = (OUT / "axioms.log").read_text(encoding="utf-8")
    seen: dict[str, list[str]] = {}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        seen[match.group(1)] = [x.strip() for x in match.group(2).split(",") if x.strip()]
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        seen[match.group(1)] = []
    expected = {d["name"] for d in declarations}
    missing = sorted(expected - seen.keys())
    bad = {name: sorted(set(axioms) - ALLOWED_AXIOMS) for name, axioms in seen.items()
           if set(axioms) - ALLOWED_AXIOMS}
    write_json("axiom_audit.json", {"allowed": sorted(ALLOWED_AXIOMS),
        "seen": seen, "missing": missing, "disallowed": bad})
    if missing or bad:
        status["axiom_audit_status"] = "FAIL"
        return finish(3, "AXIOM_AUDIT_FAILED")
    status["axiom_audit_status"] = "PASS"
    if args.scope == "modules":
        return finish(0, "MODULAR_KERNEL_PASS_FULL_EXISTENCE_STILL_UNPROVED")
    if open_obligations or FULL_THEOREM not in expected:
        return finish(4, "MODULES_PASS_BUT_FULL_T4_PROOF_INCOMPLETE")
    # A future full-proof declaration must be present and included in the same
    # kernel and axiom audits. A reviewer must additionally check its type and
    # the definitions that express the semidirect construction.
    return finish(4, "FULL_THEOREM_SEMANTIC_REVIEW_NOT_IMPLEMENTED")


if __name__ == "__main__":
    raise SystemExit(main())
