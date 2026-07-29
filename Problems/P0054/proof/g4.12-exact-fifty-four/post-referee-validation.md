# P0054 G4.12 post-Referee validation

```text
VALIDATED_BASE_HEAD: 58f005e2f0bde9103acd15d37a6a22ce16308ad9
FROZEN_SUBPROBLEM_SHA256: d3dc887cc95136d5eeecc58ddf09f8cd589d49486867a55fa7b1c20f57248957
CANDIDATE_SHA256: 34523d981c6f32e03dff873bc488c7b3832341db9459716a1d7058db495ed1ce
REFEREE_AUDIT_SHA256: e7b8b468fc6f39f12370c4f46a93d83325d74c50e813f7c566184ede8402eb02
CANDIDATE_MANIFEST_SHA256: af0093442958622c7b6a7fb52201da6fb153ce4725c2d922aadedcc2a0f85bbd
REFEREE_VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
VALIDATION_ENVIRONMENT: HOST_EXECUTION_CLONE_WITH_LOCKED_CACHES
CLAIMS_OR_STATUS_MODIFIED: NO
```

## Scope

`DEFINITION`: this record validates the repaired G4.12 candidate after the
isolated Referee accepted its arbitrary-finite proof. It does not update the
formal claim ledger, establish novelty or priority, replace human review, or
authorize public release.

## Repository checks

`COMPUTED`: the following commands completed successfully after the final
Referee verdict was saved:

```text
UV_OFFLINE=1 uv sync --locked --python 3.12
UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run pytest -q -p no:cacheprovider
UV_OFFLINE=1 uv run ruff check .
UV_OFFLINE=1 uv run mypy scripts tests
lake build
lake env lean Problems/P0054/formal/Main.lean
lake env lean Problems/P0001/formal/Main.lean
git diff --check
```

The test suite reported `178 passed`. Ruff and mypy reported no errors across
39 checked source files. Lean completed all 8,662 build jobs and accepted both
entry files. The build emitted only the pre-existing P0053 linter warnings.
The P0054 axiom audit remained limited to `propext`, `Classical.choice`, and
`Quot.sound`.

## Integrity checks

`COMPUTED`: all 18 frozen input hashes matched. The candidate manifest parsed,
and all 36 bound objects matched their declared SHA-256 values. The hashes of
`claims.yaml` and `status.md` remained equal to the frozen values.

The accepted candidate has SHA-256
`34523d981c6f32e03dff873bc488c7b3832341db9459716a1d7058db495ed1ce`.
The accepted repair changed only the proof and experiment report; no finite
enumerator or saved output changed.

## Experiment replay

`COMPUTED`: all seven C++ sources compiled with
`-O2 -Wall -Wextra -Werror -pedantic`. The regenerated outputs were
byte-identical to the saved certificates.

All independent Python implementations were replayed into temporary files.
The regenerated JSON outputs were byte-identical to the saved evidence. The
cross-checks include:

```text
Fano graphs:                              2187
Fano (8,5) candidates:                  249576
(6,10) degree-three kernel vectors:         95
(6,10) compatible extensions:                0
(8,8) five-row kernel vectors:             1890
(8,8) extension candidates:                2514
(8,8) valid extensions:                       0
(7,9) four-row kernel vectors:               136
(7,9) extension candidates:               138161
(7,9) valid extensions:                        0
(7,9) labelled six-row couplings:          90898
(7,9) minimum pair blockers:                   4
```

Each C++ source also compiled with AddressSanitizer and
UndefinedBehaviorSanitizer at `-O0`. All seven sanitized executions completed
without a diagnostic, and their outputs remained byte-identical to the saved
certificates.

Ruff and mypy accepted the independent Python verifiers. The experiment
report, Referee report, and this validation record passed the lailai-skill
checker with zero errors and zero warnings. The accepted candidate retains
15 pre-existing `math-manual-space` formatting flags outside the Lemma 8.1
repair. They do not affect the mathematics and were not changed after the
Referee bound the candidate hash.

## Verdict

`PROVED_CANDIDATE`: relative to the frozen G4.12 inputs, every possible
fifty-four-member profile is impossible. The accepted candidate consequence
is

$$
\operatorname{sat}(7)=55
$$

`COMPUTED`: the finite kernel enumerations are used only after proved
arbitrary-finite reductions. They do not independently establish the exact
value.

`UNKNOWN`: novelty, priority, and Lean formalization of the exact-value
candidate.

No change to `claims.yaml` or `status.md`, publication, expert contact, push,
authorship change, or next gate occurred in this gate.
