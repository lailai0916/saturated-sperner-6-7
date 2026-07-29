# P0054 G4.5 post-referee validation

```text
VALIDATED_COMMIT: 34dcf39
REFEREE_VERDICT: ACCEPT
VALIDATION_ENVIRONMENT: HOST_EXECUTION_CLONE_WITH_LOCKED_CACHES
CLAIMS_OR_STATUS_MODIFIED: NO
```

## Scope

`DEFINITION`: this record validates the repository after the isolated Referee
accepted the G4.5 candidate. It does not alter the Referee report, promote a
claim, or replace the required human review.

The Referee container correctly recorded that its own offline environment
lacked the pinned toolchain caches. That container-local limitation does not
apply to the host execution clone, where the same commit has access to the
locked Python 3.12.13 environment and the existing Lean cache.

## Results

`COMPUTED`: the following commands completed successfully at commit
`34dcf39`:

```text
UV_OFFLINE=1 uv sync --locked --python 3.12
UV_OFFLINE=1 uv run pytest
UV_OFFLINE=1 uv run ruff check .
UV_OFFLINE=1 uv run mypy scripts tests
lake build
lake env lean Problems/P0054/formal/Main.lean
lake env lean Problems/P0001/formal/Main.lean
git diff --check
```

The test suite reported `178 passed`. Ruff and mypy reported no errors. Lean
completed all `8662` build jobs and accepted both requested entry files. The
build emitted only the pre-existing P0053 linter warnings.

`COMPUTED`: the G4.5 finite checker was replayed through the locked Python
environment, and its standard output matched `finite-check-output.json`
byte-for-byte:

```text
UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run python \
  Problems/P0054/experiments/g4.5-coupled-layers/check_a3_blocker_lemma.py
```

This computation remains regression evidence only. The accepted arbitrary-
finite-ground-set proof does not depend on it.

## Boundary

`PROVED`: the mathematical Referee verdict remains `ACCEPT` for the candidate
lower bound `sat(7)>=48` relative to the frozen G0--G4.4 inputs.

`UNKNOWN`: exact `sat(7)`, exact `m(3,3)`, novelty, and priority. The formal
repository claim remains `sat(7)>=47` until the required human review.
