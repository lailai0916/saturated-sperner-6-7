# P0054 G2 — bounded size-54 discovery

## Frozen reference

The reference is the verified eight-core size-55 candidate at
`../certificates/core-8-target-55-selfcontained.json`, with semantic digest
`55d0a1e19a024efb944fc9a00ea466bdd6d5b11383f1bd86c1f772d8fb92acac`.

## Recorded searches

### Local neighborhood

`neighborhood-report.json` records Z3 runs at target 54 while retaining at
least 54, 53, 52, 51, 50, 49, or 48 members of the reference family.

- minimum overlap 54: `UNSAT` in 0.763 seconds;
- minimum overlap 53: `UNSAT` in 1.120 seconds;
- minimum overlap 52: `UNSAT` in 4.982 seconds;
- minimum overlaps 51 through 48: `UNKNOWN` after 45 seconds each.

These UNSAT answers have no external proof certificate and are not promoted
to theorems.  They are restricted-neighborhood `COMPUTED` results only.

### Complete baseline CNF

`portfolio-report.json` records four complete target-54 CaDiCaL 3.0.1 runs on
the original three-signature CNF.  Each configuration reached its 600-second
limit without SAT or UNSAT.

### Exact oriented CNF

`oriented/portfolio-report.json` records four CaDiCaL 3.0.1 runs on the exact
oriented encoding proved in `../../proof/size54-oriented-reduction.md`.
`kissat-oriented/portfolio-report.json` records four further Kissat 4.0.4
runs on the identical CNF.  Every configuration reached its 600-second limit
without SAT or UNSAT.

## Reproduction

```bash
uv run python -m scripts.p0054_size54_discovery neighborhood \
  --minimum-overlaps 54 53 52 51 50 49 48 \
  --timeout-seconds 45

uv run python -m scripts.p0054_size54_discovery portfolio \
  --oriented \
  --solver /opt/homebrew/bin/kissat \
  --solver-kind kissat \
  --timeout-seconds 600 \
  --workers 4 \
  --output-directory Problems/P0054/experiments/size54-g2/kissat-oriented
```

## Interpretation

No size-54 candidate was found.  No lower bound was proved.  The exact value
of `sat(7)` and feasibility at size 54 remain `UNKNOWN`.
