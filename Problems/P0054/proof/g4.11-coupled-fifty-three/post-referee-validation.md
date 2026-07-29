# P0054 G4.11 post-Referee validation

```text
VALIDATED_BASE_HEAD: bb73a8524d79621ca1aa185b82426bd4f39d5b21
FROZEN_SUBPROBLEM_SHA256: 37c422adc330ceb43ffca7b930f3da0b7c46ee5ece3d0c1da2e7186695eeca34
CANDIDATE_SHA256: 74c790f92d68728fd858aed64f3222700793db5f00a9f683c8f1699f8498b553
REFEREE_AUDIT_SHA256: a9b83c133c5d1a24a46099cadf1c89c10c016b32092430a27fde431c8410c121
REFEREE_VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
VALIDATION_ENVIRONMENT: HOST_EXECUTION_CLONE_WITH_LOCKED_CACHES
CLAIMS_OR_STATUS_MODIFIED: NO
```

## Scope

`DEFINITION`: this record validates the repaired G4.11 candidate after the
isolated Referee accepted its arbitrary-finite proof. It does not promote a
formal repository claim, replace human review, or authorize G4.12.

## Repository checks

`COMPUTED`: the following commands completed successfully after the final
Referee verdict was saved:

```text
UV_OFFLINE=1 uv sync --locked --python 3.12
UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run pytest -p no:cacheprovider
UV_OFFLINE=1 uv run ruff check .
UV_OFFLINE=1 uv run mypy scripts tests
lake build
lake env lean Problems/P0054/formal/Main.lean
lake env lean Problems/P0001/formal/Main.lean
git diff --check
```

The test suite reported `178 passed`. Ruff and mypy reported no errors across
39 checked source files. Lean completed all 8,662 build jobs and accepted
both entry files. The build emitted only the pre-existing P0053 linter
warnings. The P0054 axiom audit remained limited to `propext`,
`Classical.choice`, and `Quot.sound`.

## Experiment replay

`COMPUTED`: the final manifest parsed, and all 23 bound objects matched their
declared SHA-256 values. This includes the candidate, frozen statement, 12
frozen dependencies, four sources, four outputs, and experiment report.

All three C++ sources compiled with
`-O3 -Wall -Wextra -Werror -pedantic`. The regenerated four-row, five-row,
and extension outputs were byte-identical to the saved certificates. The
independent Python verifier used the regenerated kernel outputs and reproduced
`verification.json` byte-for-byte.

The replay returned:

```text
four-row classes:                 1
five-row multiplicity vectors: 490
five-row classes:                 8
five-row Q candidates:           55
valid extensions:                 0
three-row labelled solutions:     3
```

Each C++ source also compiled with AddressSanitizer and
UndefinedBehaviorSanitizer at `-O0`. All three sanitized executions completed
without a diagnostic, and their outputs remained byte-identical to the saved
certificates.

Ruff and mypy accepted the independent Python verifier. The lailai-skill
checker reported zero errors and zero warnings on the final candidate,
experiment report, Referee report, and this validation record. Its OI-only
C++ style rules were not applied to these research certificate programs.

## Verdict

`PROVED_CANDIDATE`: relative to the frozen G4.11 inputs, the total-53 profile
$(1,6,12,15,12,6,1)$ is impossible. The accepted candidate consequence is
$\operatorname{sat}(7)\ge54$.

`COMPUTED`: the finite kernel enumerations are used only after proved
arbitrary-finite reductions. They do not independently establish the global
lower bound.

`UNKNOWN`: exact $\operatorname{sat}(7)$, novelty, priority, and Lean
formalization of the candidate lower bound.

No change to `claims.yaml` or `status.md`, publication, expert contact, push,
or G4.12 work occurred in this gate.
