# The exact saturated 6- and 7-Sperner numbers

This repository contains the proof, Lean 4 formalization, and reproducibility
artifacts for the manuscript *The exact saturated 6- and 7-Sperner numbers* by
Jiazhi Chen.

For a fixed positive integer `k`, let `sat(k)` denote the eventual minimum size
of a saturated `k`-Sperner family in a sufficiently large Boolean lattice. The
main results are

\[
\operatorname{sat}(6)=30,
\qquad
\operatorname{sat}(7)=55.
\]

The corresponding Lean declarations are:

```lean
AiMathLab.P0054.Sat6StableExact.sat_six_eq_thirty
  : IsStableSaturationNumber 6 30
AiMathLab.P0054.Sat7StableExact.sat_seven_eq_fifty_five
  : IsStableSaturationNumber 7 55
```

Here `IsStableSaturationNumber k s` asserts the existence of a threshold `N`
such that, for every `n ≥ N`, a saturated `k`-Sperner family of cardinality `s`
exists on `Fin n` and every saturated `k`-Sperner family on `Fin n` has at
least `s` members. It is a quantified proposition, not evaluation of a Lean
function named `sat`.

[简体中文说明](README.zh-Hans.md)

## Evidence levels

The repository keeps three kinds of evidence separate:

- **PROVED**: a mathematical proof is given in the manuscript and proof notes;
- **COMPUTED**: a finite computation or solver result was independently
  checked within its recorded scope;
- **FORMALIZED**: Lean accepts the stated theorem under its reported axioms.

Both exact stable values above are **PROVED** and **FORMALIZED**. Discovery
searches and historical timeouts remain **COMPUTED** or **UNKNOWN** as marked;
they are not silently promoted to proofs. The final literature audit found no
public equivalent in its recorded search scope, but this is not an absolute
novelty or priority claim.

## Reproduce the formal verification

Prerequisites are Python 3.12, [uv](https://docs.astral.sh/uv/), and an
[elan](https://github.com/leanprover/elan)-managed Lean installation. The
locked project uses Lean `v4.33.0-rc1` and mathlib `v4.33.0-rc1`.

```bash
uv sync --locked --python 3.12
uv run ruff check .
uv run mypy
uv run pytest
lake build AiMathLab AiMathLab.P0054Sat7StableExact
lake env lean Problems/P0054/formal/Main.lean
```

The independent Lean entry point prints the axioms of both final theorems.
The expected list is exactly `propext`, `Classical.choice`, and `Quot.sound`.
The Lean source contains none of the prohibited proof bypasses `sorry`,
`admit`, `axiom`, `unsafe`, `native_decide`, or `run_tac`.

Strict mypy checking covers the hand-maintained verifier and test layer. The
mechanical Lean source generators are instead checked by deterministic replay,
generated-source comparisons, Python tests, and the final Lean kernel build;
they are intentionally not represented as fully type-annotated modules.

## Repository map

- `AiMathLab/`: Lean definitions, certificates, reductions, and final theorems;
- `Problems/P0054/formal/`: verification entry point, statement crosswalk, and
  formalization report;
- `Problems/P0054/paper/`: manuscript sources and submission materials;
- `Problems/P0054/proof/`: human-readable proof development and audits;
- `Problems/P0054/experiments/`: exact-search inputs, outputs, and compact
  certificates;
- `Problems/P0054/release/`: manifests for large archived artifacts;
- `scripts/` and `tests/`: generators, semantic verifiers, and regression
  tests.

The source repository omits large DRAT traces that exceed ordinary GitHub file
limits. The complete frozen archive, including nine CNF/DRAT pairs, is attached
to release `v1.0.0` together with its SHA-256 sidecar and is mirrored on Zenodo.
See [`artifacts/README.md`](artifacts/README.md) for the integrity boundary.
In a source-only clone, five archive-byte tests are reported as skipped. After
placing the archived paths into the working tree, set
`P0054_REQUIRE_ARCHIVE_ARTIFACTS=1` to turn every missing archive file into a
hard test failure.

## Citation and license

Machine-readable citation metadata is in [`CITATION.cff`](CITATION.cff). The
software and formalization sources are released under the Apache License 2.0;
see [`LICENSE`](LICENSE). The manuscript and mathematical statements should be
cited to the associated article and archival record once their identifiers are
available.
