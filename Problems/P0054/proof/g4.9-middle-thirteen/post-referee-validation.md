# P0054 G4.9 post-Referee validation

```text
VALIDATED_CANDIDATE_COMMIT: 6c88f28da99f9d6b831a441a46f73f05eff3bc0e
REFEREE_VERDICT: ACCEPT
VALIDATION_ENVIRONMENT: HOST_EXECUTION_CLONE_WITH_LOCKED_CACHES
CLAIMS_OR_STATUS_MODIFIED: NO
```

## Scope

`DEFINITION`: this record validates the frozen G4.9 candidate after an
isolated Referee accepted its arbitrary-finite proof. It does not alter the
Referee report, promote a formal claim, or replace human review.

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
git diff --cached --check
```

The test suite reported `178 passed`. Ruff and mypy reported no errors. Lean
completed all `8662` build jobs and accepted both requested entry files. The
build emitted only the pre-existing P0053 linter warnings. The P0054 axiom
audit remained limited to `propext`, `Classical.choice`, and `Quot.sound`.

The candidate SHA-256 remained
`c62752dfc9cdcd4a078f4b1568cd0b1ab046bc4d786a987516cf45e3940f25e1`.
All five frozen input hashes in `g4.9-middle-thirteen/frozen-subproblem.md`
matched the validated checkout. The frozen G4.9 statement SHA-256 remained
`5a2c278b69b81aab2c6e51423d263936777190e6a54eee9df5d0506750b0f1d3`.

## Boundary

`PROVED`: the mathematical Referee verdict is `ACCEPT` for the candidate lower
bound $\operatorname{sat}(7)\ge52$ relative to the frozen inputs.

`UNKNOWN`: exact $\operatorname{sat}(7)$, exact $m(3,3)$, novelty, and
priority. The formal repository claim remains
$47\le\operatorname{sat}(7)\le55$ until the required human review.

No stronger gate has been started.
