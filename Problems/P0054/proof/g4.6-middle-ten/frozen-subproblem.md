# P0054 G4.6 middle-layer total-ten problem

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_6_MIDDLE_LAYER_TOTAL_TEN
BASE_COMMIT: 4d1bb24aae909dfa8e64cac0728c004649bf7184
OFFICIAL_GLOBAL_BOUNDS: 47 <= sat(7) <= 55
INTERNAL_REFEREE_ACCEPTED_CANDIDATE: sat(7) >= 48
TARGET_IF_PROVED: sat(7) >= 49
NETWORK: LITERATURE_METADATA_ONLY; MATHEMATICS_OFFLINE
```

## Frozen inputs

The following files are immutable inputs for this gate:

| Path | SHA-256 |
|---|---|
| `Problems/P0054/proof/g4.4-exact-local/candidate-proof.md` | `5bacfe8e319ce76ac1c8e8e9efa35fe1454cf896ace8c6ee5c10d8f04b2d9832` |
| `Problems/P0054/proof/g4.5-coupled-layers/candidate-proof.md` | `41e957067396f3b83f7db4c6fba89c638ddc3894ca34d0eda804da324220f1bc` |
| `Problems/P0054/proof/g4.5-coupled-layers/referee-audit.md` | `30c7ef69bb620f104bc9c70cf9580c2cc00b227730d8a477a76130a6259c027f` |
| `Problems/P0054/proof/g4.5-coupled-layers/post-referee-validation.md` | `763c98a0d40b22661f45db4c290537a61441141111d82a1a71d940ee46a99c4c` |
| `Problems/P0054/experiments/g4.3-stronger-lower/search.py` | `ce1026519f6e9f7b3a90da6bd0ea7e1eb7fc6d6b0f7db2cadda05262488b7ec0` |

`PROVED`: the accepted G4.5 candidate recognizes the two sides of the middle
layer as finite mutual blockers. Every member on both sides has size at least
three. G4.5 proves that their total cardinality is at least ten.

`PROVED`: the frozen other-layer bounds are

```text
(|A_0|,|A_1|,|A_2|,|A_4|,|A_5|,|A_6|) >= (1,6,12,12,6,1).
```

The G4.5 mathematical result has an isolated Referee `ACCEPT` verdict and a
complete host validation, but it has not been promoted into `claims.yaml` or
`status.md` because human review remains pending.

## One objective

Determine whether every finite mutual-blocker pair whose members have size at
least three has total cardinality at least eleven. Equivalently, exclude a
middle layer with exactly ten members without imposing a bound on the finite
trace ground set.

The preferred outcome is a dependency-closed combinatorial proof. A concrete
total-ten pair would refute the target. An incidence-pattern search may guide
the proof, but a negative computation remains `COMPUTED` unless accompanied
by a proved finite reduction and an accepted proof-level certificate.

## Evidence boundary

- Allow arbitrary finite ground sets, repeated incidence patterns, inactive
  ground points, parallel actual points, nonuniform member sizes, and empty
  incidence classes.
- Preserve blocker minimality and both orientations of the mutual-blocker
  equality.
- Do not promote the G4.5 candidate or any G4.6 result into `claims.yaml` or
  `status.md` in this discovery gate.
- Do not infer novelty, priority, exact `sat(7)`, or exact `m(3,3)`.
- Do not publish, push, contact experts, or start a second mathematical
  objective in this gate.

