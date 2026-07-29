# P0054 G4.8 middle-layer total-twelve problem

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_8_MIDDLE_LAYER_TOTAL_TWELVE
BASE_COMMIT: deac9aabdb2446f7b618328bb7e0a33a7be9ea90
OFFICIAL_GLOBAL_BOUNDS: 47 <= sat(7) <= 55
INTERNAL_REFEREE_ACCEPTED_CANDIDATE: sat(7) >= 50
TARGET_IF_PROVED: sat(7) >= 51
NETWORK: MATHEMATICS_OFFLINE
```

## Frozen inputs

The following files are immutable inputs for this gate:

| Path | SHA-256 |
|---|---|
| `Problems/P0054/proof/g4.4-exact-local/candidate-proof.md` | `5bacfe8e319ce76ac1c8e8e9efa35fe1454cf896ace8c6ee5c10d8f04b2d9832` |
| `Problems/P0054/proof/g4.7-middle-eleven/candidate-proof.md` | `cd396493710810fa28d8564ed4fe1864aa6fcf5df3fd311aaa8084afc4c0b494` |
| `Problems/P0054/proof/g4.7-middle-eleven/referee-audit.md` | `ac1a4c592c21d2ff2cb107070fe6901dc89c1c0cce1a86610f55d3cb847c0b96` |
| `Problems/P0054/proof/g4.7-middle-eleven/post-referee-validation.md` | `4df471afdc7d46a03213e705d122eac9a2984f332ba8f8f44e7f8c90c969f294` |
| `Problems/P0054/experiments/g4.3-stronger-lower/search.py` | `ce1026519f6e9f7b3a90da6bd0ea7e1eb7fc6d6b0f7db2cadda05262488b7ec0` |
| `Problems/P0054/experiments/g4.6-middle-ten/results.json` | `8ea53c6fcdf415ab2f6ec662bbe42569aec15cd47d51698d0cbb7e3ff1b1ce3c` |

`PROVED`: the accepted G4.7 candidate recognizes the two sides of the middle
layer as finite mutual blockers. Every member on both sides has size at least
three, and their total cardinality is at least twelve.

`PROVED`: the frozen other-layer bounds are

```text
(|A_0|,|A_1|,|A_2|,|A_4|,|A_5|,|A_6|) >= (1,6,12,12,6,1).
```

The G4.7 result has an isolated Referee `ACCEPT` verdict and complete host
validation. G4.5--G4.7 have not been promoted into `claims.yaml` or
`status.md` because human review remains pending.

## One objective

Determine whether every finite mutual-blocker pair whose members have size at
least three has total cardinality at least thirteen. By the accepted G4.7
lemmas, a total-twelve counterexample must have side sizes `(5,7)` or `(6,6)`,
up to exchange.

A concrete admissible pair in either split refutes the target. A negative
incidence-pattern search remains `COMPUTED` unless accompanied by a complete
arbitrary-finite combinatorial proof.

## Evidence boundary

- Allow arbitrary finite ground sets, inactive points, loops, parallel actual
  points, repeated incidence patterns, nonuniform member sizes, and empty
  incidence classes.
- Preserve blocker minimality and both orientations of mutual-blocker equality.
- Treat `(5,7)` and `(6,6)` as separate obligations; do not combine partial
  arguments into a proof of the total-twelve exclusion.
- Do not promote G4.5--G4.8 into `claims.yaml` or `status.md` in this discovery
  gate.
- Do not infer novelty, priority, exact `sat(7)`, or exact `m(3,3)`.
- Do not publish, push, contact experts, or start a second mathematical
  objective in this gate.
