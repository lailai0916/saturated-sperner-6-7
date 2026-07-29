# P0054 G4.8 post-referee validation

```text
VALIDATED_COMMIT: 1b6138e
REFEREE_VERDICT: ACCEPT
VALIDATION_ENVIRONMENT: HOST_EXECUTION_CLONE_WITH_LOCKED_CACHES
CLAIMS_OR_STATUS_MODIFIED: NO
```

## Scope

`DEFINITION`: this record validates the G4.8 candidate after an isolated
Referee accepted its arbitrary-finite proof. It does not alter the Referee
report, promote a formal claim, or replace human review.

## Results

`COMPUTED`: the following commands completed successfully after the Referee
report was saved:

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

The candidate SHA-256 remained
`5bb6f43906a9048cd87a861569d4ed729ab6a2f83bf334943344b1c55dbd09e0`.
All six frozen input hashes in `g4.8-middle-twelve/frozen-subproblem.md`
matched the validated checkout.

## Boundary

`PROVED`: the mathematical Referee verdict is `ACCEPT` for the candidate lower
bound `sat(7)>=51` relative to the frozen G0--G4.7 inputs.

`UNKNOWN`: exact `sat(7)`, exact `m(3,3)`, thirteen-member compatibility,
novelty, and priority. The formal repository claim remains `sat(7)>=47` until
the required human review.
