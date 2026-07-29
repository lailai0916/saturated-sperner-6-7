# P0054 G4.10 post-Referee validation

```text
VALIDATED_BASE_HEAD: 5b35bda08342279db986dca5971434182ee9d2b7
FROZEN_SUBPROBLEM_SHA256: c82b485af00399be79f36be46d8b6cece90dd4828a9a065d148305ea71410db4
CANDIDATE_SHA256: 5525e73d5d25394f2e35bcf051968243fb70597e63daa43e9fc0e773b853d454
REFEREE_VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
VALIDATION_ENVIRONMENT: HOST_EXECUTION_CLONE_WITH_LOCKED_CACHES
CLAIMS_OR_STATUS_MODIFIED: NO
```

## Scope

`DEFINITION`: this record validates the G4.10 candidate after the isolated
Referee accepted its arbitrary-finite proof. It does not promote a formal
claim, replace human review, or authorize G4.11.

## Repository checks

`COMPUTED`: the following commands completed successfully after the Referee
report was saved:

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

The test suite reported `178 passed`. Ruff and mypy reported no errors. Lean
completed all 8,662 build jobs and accepted both entry files. The build
emitted only the pre-existing P0053 linter warnings. The P0054 axiom audit
remained limited to `propext`, `Classical.choice`, and `Quot.sound`.

## Experiment replay

`COMPUTED`: the final manifest parsed and all eight bound file hashes matched.
The frozen statement hash and all seven frozen dependency hashes also matched.

The Python support checker reproduced
`support-multigraph-results.json` byte-for-byte. Both C++ sources compiled
with `-O3 -Wall -Wextra -Werror -pedantic`. The four-row program reproduced
41 kernel classes. The seven-row program was run against both the regenerated
and saved kernel reports; both runs reproduced six valid vectors and zero
non-Fano vectors byte-for-byte.

The final Python source hash is
`4dd7168574b9f1e2e0332a4851e46ec2f1215af183de0513aa800373cf025587`.
It includes the post-audit `zip(..., strict=True)` safety edit. Two independent
final-source replays reproduced the saved JSON exactly.

Both C++ programs also passed combined AddressSanitizer and
UndefinedBehaviorSanitizer execution. Their sanitized outputs remained
byte-identical to the saved certificates.

The lailai-skill checker reported zero errors and zero warnings on the final
candidate, experiment report, and Referee report. Its OI-only C++ style rules
were not applied to these research certificate programs.

## Verdict

`PROVED_CANDIDATE`: relative to the frozen G4.10 inputs, the total-52 equality
profile is impossible. The accepted candidate consequence is
$\operatorname{sat}(7)\ge53$.

`COMPUTED`: finite enumeration is used only after the proved arbitrary-finite
reductions. It does not independently prove the global lower bound.

`UNKNOWN`: exact $\operatorname{sat}(7)$, novelty, priority, and Lean
formalization of the new lower bound.

No change to `claims.yaml` or `status.md`, publication, expert contact, push,
or G4.11 work occurred in this gate.
