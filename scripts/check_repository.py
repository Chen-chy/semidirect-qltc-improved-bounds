#!/usr/bin/env python3
"""Offline file/link, dependency-index, syntax and Lean-source-screen checks.

This is deliberately not a theorem checker or a substitute for Lean.
"""
from __future__ import annotations

import ast
import importlib.util
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
# The release inventory excludes transient runtime reports.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from manifest import snapshot_files


def anchors(text: str) -> set[str]:
    result = set(re.findall(r'<a\s+id="([^"]+)"', text))
    counts: dict[str, int] = {}
    for line in text.splitlines():
        match = re.match(r"^#{1,6}\s+(.+?)\s*#*\s*$", line)
        if not match:
            continue
        slug = re.sub(r"[^\w\- ]", "", match.group(1).lower()).replace(" ", "-")
        occurrence = counts.get(slug, 0)
        result.add(slug if occurrence == 0 else f"{slug}-{occurrence}")
        counts[slug] = occurrence + 1
    return result


def check_link(owner: Path, raw: str, errors: list[str]) -> bool:
    url = urlsplit(raw)
    if url.scheme in {"https", "http", "mailto"}:
        return False  # External availability is not claimed by an offline test.
    if url.scheme or raw.startswith("/"):
        errors.append(f"Nonportable link in {owner.relative_to(ROOT)}: {raw}")
        return True
    target = (owner.parent / unquote(url.path)).resolve() if url.path else owner
    if not target.is_relative_to(ROOT) or not target.exists():
        errors.append(f"Missing/local-escape link in {owner.relative_to(ROOT)}: {raw}")
    elif url.fragment and target.suffix == ".md":
        if unquote(url.fragment) not in anchors(target.read_text(encoding="utf-8")):
            errors.append(f"Missing anchor in {owner.relative_to(ROOT)}: {raw}")
    return True


def main() -> int:
    errors: list[str] = []
    files = list(snapshot_files())
    md_files = [p for p in files if p.suffix == ".md"]
    links = 0
    for path in md_files:
        text = path.read_text(encoding="utf-8")
        # Generated local download links and opaque chat citation markers do not
        # belong in a public repository. The patterns are assembled here so this
        # checker does not flag its own source text in broader scans.
        for bad in ("sandbox:" + "/", "/mnt/" + "data/", "\ue200cite\ue202", "\ue200filecite\ue202"):
            if bad in text:
                errors.append(f"Nonportable chat artifact in {path.relative_to(ROOT)}")
        if len(re.findall(r"^\$\$\s*$", text, re.M)) % 2:
            errors.append(f"Unbalanced display-math fences in {path.relative_to(ROOT)}")
        # Our authoring style uses simple inline Markdown links, without nested
        # parentheses or titles. This check does not claim a full Markdown parser.
        for raw in re.findall(r"\[[^\]\n]*\]\(([^\s)]+)\)", text):
            links += check_link(path, raw, errors)
    py_files = [p for p in files if p.suffix == ".py"]
    for path in py_files:
        try:
            ast.parse(path.read_text(encoding="utf-8"), filename=str(path.relative_to(ROOT)),
                      feature_version=(3, 10))
        except SyntaxError as exc:
            errors.append(str(exc))
    for path in (p for p in files if p.suffix == ".json"):
        try:
            json.loads(path.read_text(encoding="utf-8"))
        except (ValueError, UnicodeError) as exc:
            errors.append(f"Invalid JSON {path.relative_to(ROOT)}: {exc}")
    data = json.loads((ROOT / "claims.json").read_text(encoding="utf-8"))
    indexed = {item["id"]: item for item in data["claims"]}
    if len(indexed) != len(data["claims"]):
        errors.append("Duplicate claim IDs")
    for item in data["claims"]:
        check_link(ROOT / "claims.json", item["location"], errors)
        if item["lean_kernel_verified"]:
            errors.append(f"Unsupported kernel status for {item['id']}")
        for dep in item["depends_on"]:
            if dep not in indexed:
                errors.append(f"Unknown dependency {dep}")
    active: set[str] = set()
    done: set[str] = set()
    def visit(node: str):
        if node in active:
            errors.append(f"Cyclic claim dependency at {node}")
            return
        if node in done or node not in indexed:
            return
        active.add(node)
        for dep in indexed[node]["depends_on"]:
            visit(dep)
        active.remove(node)
        done.add(node)
    for node in indexed:
        visit(node)
    status = json.loads((ROOT / "STATUS.json").read_text(encoding="utf-8"))
    if status["lean"]["kernel"] != "NOT_RUN" or status["lean"]["full_existence"] != "NOT_PROVED":
        errors.append("This snapshot has no evidence supporting upgraded Lean status")
    # Reuse the archived lexical screen, but DO NOT invoke its build routine.
    path = ROOT / "formalization/lean4/tools/verify.py"
    spec = importlib.util.spec_from_file_location("lean_source_auditor", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load Lean lexical auditor")
    auditor = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(auditor)
    declarations, violations, hashes = auditor.inventory()
    if violations:
        errors.append(f"Lean lexical screen rejected {len(violations)} entries")
    report = {
        "result": "FAIL" if errors else "PASS_REPOSITORY_CHECKS_ONLY",
        "markdown_files": len(md_files), "local_links_checked": links,
        "python_syntax_files": len(py_files), "claims": len(indexed),
        "lean_public_declarations_in_source": len(declarations),
        "lean_lexical_screen": "FAIL" if violations else "PASS_LEXICAL_ONLY",
        "lean_kernel": "NOT_RUN", "external_links_fetched": False,
        "errors": errors,
    }
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
