# P0054 G3 structural size-54 evidence

## Strictly proved artifacts

- `size54-g3-layer-bounds/verification-manifest.json` records four UNSAT CNFs
  and four independently accepted DRAT proofs.  Together with complement
  duality and explicit witnesses, they prove the exact independent layer
  minima `(1,6,12,14,12,6,1)`.
- `size54-g3-system/fixed-middle14/verification-manifest.json` records a
  checked DRAT proof that the displayed sharp 14-member middle layer cannot be
  extended to a full size-at-most-54 system.

The checker is DRAT-trim at commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`.  Manifests contain checker,
solver, CNF, proof, log, and semantic hashes.

## Computed-only artifacts

- `size54-g3-system/complete/verification-manifest.json`: complete reduced
  model, 1,800-second timeout.
- `size54-g3-profiles/profile-search-manifest.json`: all 28 two-slack profiles,
  60 seconds each, all timeout.
- `size54-g3-layer-bounds/core8-layer3-at-most-16.kissat.log`: exploratory SAT
  run from which the valid 14-member middle witness was extracted.  Its
  solver proof-trace output was not a proof and was removed.

The 4.9 GB incomplete trace from the complete timeout was also removed.  It
had no verification status or mathematical value and can be regenerated from
the deterministic CNF and recorded command.

## Reproduction

```bash
git clone https://github.com/marijnheule/drat-trim.git /tmp/p0054-drat-trim
git -C /tmp/p0054-drat-trim checkout 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
make -C /tmp/p0054-drat-trim

UV_OFFLINE=1 uv run python -m scripts.p0054_size54_structural \
  --solver /opt/homebrew/bin/kissat \
  --checker /tmp/p0054-drat-trim/drat-trim \
  --timeout-seconds 1800
```

No result in this directory proves a global lower bound for `sat(7)`.
