#!/usr/bin/env python3
"""Export MonoidProduct Lean modules into this repository and guard them.

Usage:
    python3 scripts/export-monoid.py SOURCE_DIR MODULE [MODULE ...]
    python3 scripts/export-monoid.py SOURCE_DIR --modules-file LIST.txt
    python3 scripts/export-monoid.py --check-only [--modules-file LIST.txt]

Each form also accepts --forbidden-file PATTERNS.txt.

SOURCE_DIR is the root of a Lean package containing the modules (so that
module `MonoidProduct.Foo.Bar` lives at `SOURCE_DIR/MonoidProduct/Foo/Bar.lean`).
Module names may be given with or without the `MonoidProduct.` prefix; the
root module `MonoidProduct` maps to `MonoidProduct.lean`. A modules file lists
one module per line; blank lines and lines starting with `#` are ignored.

The script copies each module into the repository (next to this `scripts/`
directory), then scans every copied file and fails with a nonzero exit code,
listing `file:line`, when a file

  (a) matches a forbidden pattern (links to working notes, internal planning
      labels, or references to unpublished drafts; extra patterns come from
      the untracked file scripts/forbidden-patterns.local.txt, if present,
      or from --forbidden-file), or
  (b) imports a module that is neither in the publish list nor provided by
      Mathlib, QuantumQueryComplexity, Sunflower, or the Lean core.

With `--check-only`, nothing is copied: the script scans the files already
present under `MonoidProduct/` (and `MonoidProduct.lean`,
`MonoidProductChecks.lean`); the publish list then defaults to the modules
found there. The script never rewrites file contents.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LIB = "MonoidProduct"

# Generic patterns that should not appear in published Lean sources: links to
# Markdown working notes, planning labels, and section-sign references to
# unpublished drafts.
FORBIDDEN = [
    r"\.md\b",
    r"\bMilestone\b",
    r"\bTier [A-D]",
    r"followup",
    r"§",
]

# Additional patterns (one regular expression per line; blank lines and lines
# starting with `#` are ignored) are read from this file when it exists. It is
# not tracked, so maintainers can guard against names of local working files
# without publishing them. `--forbidden-file` names a different file.
LOCAL_FORBIDDEN = REPO / "scripts" / "forbidden-patterns.local.txt"

# Import roots that may be imported without being in the publish list.
ALLOWED_ROOTS = ("Mathlib", "QuantumQueryComplexity", "Sunflower", "Init", "Std", "Lean")

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.*)$")


def forbidden_patterns(extra: Path | None) -> list[tuple[str, re.Pattern[str]]]:
    pats = list(FORBIDDEN)
    path = extra if extra is not None else LOCAL_FORBIDDEN
    if path.exists():
        pats += read_list(path)
    elif extra is not None:
        raise SystemExit(f"error: forbidden-pattern file not found: {extra}")
    return [(p, re.compile(p)) for p in pats]


def normalize(name: str) -> str:
    name = name.strip()
    if name.endswith(".lean"):
        name = name[: -len(".lean")].replace("/", ".")
    if name != LIB and not name.startswith(LIB + "."):
        name = f"{LIB}.{name}"
    return name


def module_path(root: Path, module: str) -> Path:
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def read_list(path: Path) -> list[str]:
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            out.append(line)
    return out


def imported_modules(text: str) -> list[tuple[int, str]]:
    """Return (line number, module) for each import in the file header."""
    out = []
    in_block_comment = 0
    for i, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        # Track nested block comments (module docstrings precede imports only
        # in malformed files, but be tolerant).
        opens = stripped.count("/-")
        closes = stripped.count("-/")
        if in_block_comment:
            in_block_comment += opens - closes
            continue
        if stripped.startswith("/-"):
            in_block_comment = opens - closes
            continue
        m = IMPORT_RE.match(line)
        if m:
            for mod in m.group(1).split("--")[0].split():
                out.append((i, mod))
    return out


def allowed_import(mod: str, publish: set[str]) -> bool:
    if mod in publish:
        return True
    root = mod.split(".", 1)[0]
    return root in ALLOWED_ROOTS


def scan(files: list[Path], publish: set[str],
         forbidden: list[tuple[str, re.Pattern[str]]]) -> list[str]:
    problems = []
    for f in files:
        rel = f.relative_to(REPO)
        text = f.read_text(encoding="utf-8")
        for i, line in enumerate(text.splitlines(), start=1):
            for pat, rx in forbidden:
                if rx.search(line):
                    problems.append(f"{rel}:{i}: forbidden pattern {pat!r}: {line.strip()}")
        for i, mod in imported_modules(text):
            if not allowed_import(mod, publish):
                problems.append(f"{rel}:{i}: import of unpublished module {mod}")
    return problems


def existing_files() -> list[Path]:
    files = sorted((REPO / LIB).rglob("*.lean")) if (REPO / LIB).is_dir() else []
    for extra in (f"{LIB}.lean", f"{LIB}Checks.lean"):
        if (REPO / extra).is_file():
            files.append(REPO / extra)
    return files


def module_of(path: Path) -> str:
    return ".".join(path.relative_to(REPO).with_suffix("").parts)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("source", nargs="?", help="source package root (omit with --check-only)")
    ap.add_argument("modules", nargs="*", help="modules to publish")
    ap.add_argument("--modules-file", type=Path, help="file listing modules, one per line")
    ap.add_argument("--forbidden-file", type=Path,
                    help="extra forbidden patterns (default: scripts/forbidden-patterns.local.txt, if present)")
    ap.add_argument("--check-only", action="store_true", help="scan files already in the repository")
    args = ap.parse_args()

    names = list(args.modules)
    if args.modules_file:
        names += read_list(args.modules_file)

    if args.check_only:
        if args.source:
            names.insert(0, args.source)
        files = existing_files()
        publish = {normalize(n) for n in names} | {module_of(f) for f in files}
        copied = 0
    else:
        if not args.source or not names:
            ap.error("SOURCE_DIR and at least one module are required")
        src = Path(args.source).expanduser().resolve()
        if not src.is_dir():
            ap.error(f"source directory not found: {src}")
        publish = {normalize(n) for n in names}
        missing = [m for m in sorted(publish) if not module_path(src, m).is_file()]
        if missing:
            for m in missing:
                print(f"error: module {m} not found in source", file=sys.stderr)
            return 2
        files = []
        for m in sorted(publish):
            dst = module_path(REPO, m)
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(module_path(src, m), dst)
            files.append(dst)
        copied = len(files)
        stale = [module_of(f) for f in existing_files()
                 if f.parent != REPO and module_of(f) not in publish]
        for m in stale:
            print(f"export-monoid: warning: {m} is in the repository but not in the publish list")
        # Also guard the hand-written checks file, if present.
        checks = REPO / f"{LIB}Checks.lean"
        if checks.is_file():
            files.append(checks)

    # The root module always exists in the repository (as a placeholder until
    # it is exported), so the checks file may import it.
    publish.add(LIB)
    problems = scan(files, publish, forbidden_patterns(args.forbidden_file))
    sys.stdout.flush()
    lines = sum(len(f.read_text(encoding="utf-8").splitlines()) for f in files)
    print(f"export-monoid: {copied} module(s) copied, {len(files)} file(s) scanned, "
          f"{lines} line(s), {len(publish)} module(s) in the publish list")
    if problems:
        print(f"export-monoid: FAILED with {len(problems)} problem(s):", file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1
    print("export-monoid: OK (no forbidden patterns, all imports resolved)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
