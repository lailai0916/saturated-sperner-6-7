# P0054 G4.14 promotion audit

```text
GATE: P0054_G4_14_EXACT_VALUE_PROMOTION
BASE_COMMIT: 58f005e2f0bde9103acd15d37a6a22ce16308ad9
MANIFEST: Problems/P0054/proof/g4.14-exact-value-integration/integration-manifest.json
MANIFEST_SHA256: f5334532ac7ac976fc4ce0354f31913a7e9087f0d3e7c7fa203d9169ec8b2338
BOUND_OBJECTS: 33/33
PROTECTED_OBJECTS: 126/126
EXACT_VALUE_LABEL: PROVED
WORKFLOW_STATUS: SOLVED_CANDIDATE
GLOBAL_EXACT_VALUE_LEAN: NOT_FULLY_FORMALIZED
NOVELTY_AND_PRIORITY: UNKNOWN
VERDICT: PASS
```

## Scope

`DEFINITION`: this gate integrates the accepted G4.10 through G4.13 evidence
into the claim ledger, project status, formalization reports, and bilingual
internal-review manuscript. It does not alter the accepted proofs, authorize
publication, establish novelty or priority, or replace independent human
review.

The epistemic promotion and the workflow promotion are distinct. P0054-C28
records `sat(7)=55` as `PROVED`. The project is `SOLVED_CANDIDATE`, not
`SOLVED`, because independent human review remains pending.

## Evidence chain

- `PROVED`: G4.10 excludes the total-52 equality profile and gives
  `sat(7)>=53`.
- `PROVED`: G4.11 excludes the total-53 equality profile and gives
  `sat(7)>=54`.
- `PROVED`: G4.12 excludes both possible 54-member profiles on an arbitrary
  finite trace ground set. Its finite enumerations occur only after proved
  exhaustive reductions.
- `PROVED`: the explicit 55-member construction gives `sat(7)<=55`.
- `PROVED`: the two inequalities give `sat(7)=55`.
- `FORMALIZED`: G4.13 proves the local five-row degree-three kernel exclusion
  used in the G4.12 `(8,8)` branch.
- `NOT_FULLY_FORMALIZED`: Lean does not yet formalize the other G4.12
  branches, the global canonical reduction, or the eventual stable-number
  definition.
- `UNKNOWN`: novelty, priority, and independent expert acceptance.

## Integrity verification

`COMPUTED`: the upstream manifests and the G4.14 integration manifest parsed
and matched all declared SHA-256 values:

```text
G4.10:  8/8
G4.11: 23/23
G4.12: 36/36
G4.14: 33/33
```

The 126-object protected snapshot also matched byte for byte after all replay
and repository checks. It covers the accepted G4.10 through G4.13 proofs,
experiment sources and outputs, Referee records, and G4.13 Lean sources.

## Experiment replay

`COMPUTED`: every G4.10, G4.11, and G4.12 C++ enumerator was rebuilt with
warnings enabled. Regenerated primary outputs matched the saved evidence byte
for byte. Independent Python implementations were replayed against the saved
inputs, and every generated JSON report also matched byte for byte.

The G4.12 replay covered the Fano branches and all middle splits `(5,11)`,
`(6,10)`, `(7,9)`, and `(8,8)`, including their kernel and extension
cross-checks. The separate `sat(6)` incidence search returned
`STABLE_REPLAY_MATCH`; it remains a `COMPUTED` cross-check rather than a proof
dependency.

## Manuscript verification

The English and Simplified-Chinese manuscripts compiled successfully. The
English PDF has 14 A4 pages and the Chinese PDF has 15 A4 pages. Their logs
contain no undefined references, multiply defined references, overfull boxes,
or underfull boxes. The Chinese build emits only the non-fatal system-font
script warnings recorded by `fontspec`.

PDF text extraction resolves the repaired Chinese references to Lemma 3.2,
Proposition 6.2, and Corollary 5.4. Full contact sheets and focused page checks
found no clipping, overlap, or missing content on the title pages, exact-value
proofs, exhaustive-reduction tables, or reference pages.

## Repository verification

The following checks completed successfully:

```text
UV_OFFLINE=1 uv sync --locked --python 3.12
UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run --offline pytest -q -p no:cacheprovider
UV_OFFLINE=1 uv run --offline ruff check .
UV_OFFLINE=1 uv run --offline mypy scripts tests
lake build
lake env lean Problems/P0054/formal/Main.lean
lake env lean Problems/P0001/formal/Main.lean
git diff --check
```

The test suite reported `178 passed`. Lake completed all 8,662 jobs. The only
build diagnostics were the pre-existing P0053 linter warnings. Both Lean entry
files were accepted. The P0054 declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The claim ledger contains 29 unique claims, no unresolved dependency, and four
open claims. Every open claim is labeled `UNKNOWN`. The lailai-skill checker
reported no errors on the integration diff.

## Verdict

`PASS`: the repository evidence supports P0054-C28 with label `PROVED`:

```text
sat(7) = 55.
```

The final workflow state is `SOLVED_CANDIDATE`. Only independent human review
may promote it to `SOLVED`. No network research, expert contact, public release,
submission, commit, or push occurred in G4.14.
