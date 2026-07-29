# P0054 experiment boundary

Run a bounded calibration with:

```bash
uv run python scripts/p0054_layered_sat7.py calibrate \
  --core-sizes 4 5 6 7 --target-size 55 --timeout-seconds 60
```

The JSON output is labeled `COMPUTED`.  A solver `UNSAT` result has the explicit
marker `NO_EXTERNAL_CERTIFICATE_NOT_A_THEOREM`; it may guide the next engineering
step but cannot support a mathematical lower bound.

For small layers already reported UNSAT, generate a deterministic DIMACS formula
and a proof-logging solver trace with:

```bash
uv run python scripts/p0054_layered_sat7.py certify \
  --core-sizes 4 5 6 7 --target-size 55 \
  --solver /absolute/path/to/kissat
```

The trace still requires an independent DRAT checker, and the CNF-to-mathematics
reduction remains a separate proof obligation.

## Size-55 construction

`certificates/core-8-target-55-selfcontained.json` contains the exact solver
model, including all 55 templates.  Correctness does not trust the solver:

```bash
uv run python -m scripts.p0054_verify_candidate
```

This regenerates `core-8-size-55-dual-verification.json` by running the two
P0054 layer verifiers and the two independent P0053 union-level verifiers.
