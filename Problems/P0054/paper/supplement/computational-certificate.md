# Computational certificate supplement

## Trust separation

The SAT solver discovered the 55-member family but is not trusted for its
correctness.  The general construction is proved by the maximal-small-free
lemma and layering certificate in the manuscript.  Independent finite
verifiers and Lean provide redundant checks.

The human-readable saturation proof has its own narrow checker.  For each of
the seven rows it enumerates all 256 core masks, recomputes the inclusion-
maximal masks that contain no displayed small member, and checks exact equality
with the displayed large-core list.  It is run as part of:

```bash
uv run python -m scripts.p0054_verify_candidate
```

The seven-core lower bound is different: it is a computer-assisted theorem
whose trusted chain consists of the mathematical CNF reduction, a deterministic
CNF file, a DRAT proof, and independent DRAT-trim acceptance.

## Frozen identifiers

- expanded family semantic SHA-256:
  `8277267a7a9cbc6040432a9d6ffc3f16c540a6013b78bedbd85e6b1e27adde0f`;
- Lean witness-table semantic SHA-256:
  `6593d440b082ff49be9bfdd55123d981f475f8ba718f58c4ad2d471daf2c9ca7`;
- seven-core target-55 CNF: 100,297 variables and 252,427 clauses;
- checked DRAT proof size: 253,731,315 bytes;
- DRAT-trim verification result: `s VERIFIED`.

Exact file hashes and commands are recorded in:

- `Problems/P0054/experiments/certificates/verification-manifest.json`;
- `Problems/P0054/formal/witness-table-manifest.json`;
- `Problems/P0054/experiments/README.md`.

## Negative control

The withdrawn 54-member family from arXiv:2402.14113v1/v2 is rejected by the
current verifier because its third layer fails to cover core set `{2,3,6}`.
This control guards against accepting the previously reported erroneous bound.
