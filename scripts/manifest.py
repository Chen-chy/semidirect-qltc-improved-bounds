#!/usr/bin/env python3
"""Write or check the release snapshot manifest, excluding runtime products."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "MANIFEST.sha256"
SKIP_PARTS = {".git", ".artifacts", "__pycache__", ".lake", ".venv"}


def snapshot_files(root: Path = ROOT):
    for path in sorted(root.rglob("*")):
        rel = path.relative_to(root)
        if not path.is_file() or any(part in SKIP_PARTS for part in rel.parts):
            continue
        if path.is_symlink():
            raise ValueError(f"Symlinks are not permitted in a release: {rel}")
        if rel.as_posix() == "MANIFEST.sha256":
            continue
        if rel.as_posix().startswith("formalization/lean4/verification/"):
            continue
        if rel.as_posix() == "formalization/lean4/lake-manifest.json":
            continue
        if path.suffix in {".pyc", ".pyo"} or path.name == ".DS_Store":
            continue
        yield path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true")
    group.add_argument("--write", action="store_true")
    args = parser.parse_args()
    records = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in snapshot_files()}
    if args.write:
        MANIFEST.write_text("".join(f"{digest}  {path}\n" for path, digest in records.items()),
                            encoding="utf-8")
        print(f"Wrote {len(records)} release file hashes. This is not a correctness proof.")
        return 0
    if not MANIFEST.exists():
        print("Missing release manifest", file=sys.stderr)
        return 1
    expected = {}
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        digest, path = line.split("  ", 1)
        if path in expected:
            print(f"Duplicate manifest path: {path}", file=sys.stderr)
            return 1
        expected[path] = digest
    changed = sorted(p for p in set(records) | set(expected) if records.get(p) != expected.get(p))
    if changed:
        print("Manifest mismatch:\n" + "\n".join(changed), file=sys.stderr)
        return 1
    print(f"PASS: {len(records)} release files match the manifest.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
