# Contributing

Use the Lean version in `lean-toolchain` and the dependencies pinned by
`lake-manifest.json`. Start with `lake exe cache get`, then build the affected
modules. `LEAN_NUM_THREADS=1` is useful on machines with limited memory.

## Library boundaries

Keep the `MonoidProduct.*` module hierarchy. Library modules may import only
other `MonoidProduct` modules, Mathlib, QuantumQueryComplexity, Sunflower, and
the Lean core; `python3 scripts/export-monoid.py --check-only` enforces this.

Give public definitions and theorems docstrings describing their mathematical
meaning, hypotheses, and query costs, and record the corresponding paper
result in `docs/monoid-product/PAPER_CORRESPONDENCE.md`. The project permits
only `propext`, `Classical.choice`, and `Quot.sound` as proof axioms; add each
new headline theorem to `MonoidProductChecks.lean`.

## Verification

```sh
LEAN_NUM_THREADS=1 lake build
python3 scripts/export-monoid.py --check-only
```

## Releases

Document changes in `CHANGELOG.md`, including public API and Lean/Mathlib
compatibility changes, and update the `version` fields in `lakefile.toml`,
`CITATION.cff`, and `.zenodo.json`. Release tags use `vMAJOR.MINOR.PATCH`.
Do not move a published release tag.
