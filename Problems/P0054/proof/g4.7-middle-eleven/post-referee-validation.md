# P0054 G4.7 post-referee validation

```text
VALIDATED_COMMIT: 03484ce
REFEREE_VERDICT: ACCEPT
VALIDATION_ENVIRONMENT: HOST_EXECUTION_CLONE_WITH_LOCKED_CACHES
CLAIMS_OR_STATUS_MODIFIED: NO
```

## Scope

`DEFINITION`: this record validates the G4.7 candidate after an isolated
Referee accepted its arbitrary-finite proof. It does not alter the Referee
report, promote a formal claim, or replace human review.

## Results

`COMPUTED`: the following commands completed successfully in the reviewed
checkout:

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

`COMPUTED`: the frozen G4.6 incidence-pattern search was replayed through the
locked Python environment, and its standard output matched
`experiments/g4.6-middle-ten/results.json` byte-for-byte. The search remains
regression evidence only and is not a dependency of G4.7.

All five frozen input hashes in `g4.7-middle-eleven/frozen-subproblem.md`
match the validated checkout.

## Boundary

`PROVED`: the mathematical Referee verdict is `ACCEPT` for the candidate lower
bound `sat(7)>=50` relative to the frozen G0--G4.6 inputs.

`UNKNOWN`: exact `sat(7)`, exact `m(3,3)`, equality-case compatibility,
novelty, and priority. The formal repository claim remains `sat(7)>=47` until
the required human review.
