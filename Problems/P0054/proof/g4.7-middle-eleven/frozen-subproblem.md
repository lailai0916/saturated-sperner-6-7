# P0054 G4.7 middle-layer total-eleven problem

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_7_MIDDLE_LAYER_TOTAL_ELEVEN
BASE_COMMIT: d7b9fb7be9a38dc4aab6f36677fe5972b80b1726
OFFICIAL_GLOBAL_BOUNDS: 47 <= sat(7) <= 55
INTERNAL_REFEREE_ACCEPTED_CANDIDATE: sat(7) >= 49
TARGET_IF_PROVED: sat(7) >= 50
NETWORK: MATHEMATICS_OFFLINE
```

## Frozen inputs

The following files are immutable inputs for this gate:

| Path | SHA-256 |
|---|---|
| `Problems/P0054/proof/g4.4-exact-local/candidate-proof.md` | `5bacfe8e319ce76ac1c8e8e9efa35fe1454cf896ace8c6ee5c10d8f04b2d9832` |
| `Problems/P0054/proof/g4.6-middle-ten/candidate-proof.md` | `bebe22bea1bf9021ec02a6e60ebbe2b2499de2bf15bea0769c24ea66c2d70c15` |
| `Problems/P0054/proof/g4.6-middle-ten/referee-audit.md` | `ce1e6703c29ef7c8e5d7baffcf711d6e2486e159a707934f531a5006514da7f4` |
| `Problems/P0054/experiments/g4.6-middle-ten/results.json` | `8ea53c6fcdf415ab2f6ec662bbe42569aec15cd47d51698d0cbb7e3ff1b1ce3c` |
| `Problems/P0054/experiments/g4.3-stronger-lower/search.py` | `ce1026519f6e9f7b3a90da6bd0ea7e1eb7fc6d6b0f7db2cadda05262488b7ec0` |

`PROVED`: the accepted G4.6 candidate recognizes the two sides of the middle
layer as finite mutual blockers. Every member on both sides has size at least
three, and their total cardinality is at least eleven.

`PROVED`: the frozen other-layer bounds are

```text
(|A_0|,|A_1|,|A_2|,|A_4|,|A_5|,|A_6|) >= (1,6,12,12,6,1).
```

The G4.6 result has an isolated Referee `ACCEPT` verdict, but neither G4.5 nor
G4.6 has been promoted into `claims.yaml` or `status.md` because human review
remains pending.

## One objective

Determine whether every finite mutual-blocker pair whose members have size at
least three has total cardinality at least twelve. By the accepted G4.6
lemmas, a total-eleven counterexample must have side sizes `(5,6)` up to
exchange.

The preferred outcome is a dependency-closed combinatorial proof on arbitrary
finite ground sets. The G4.6 incidence-pattern search found no `(5,6)` pair,
but that result remains `COMPUTED` and is not a proof dependency.

## Evidence boundary

- Allow arbitrary finite ground sets, inactive points, loops, parallel actual
  points, repeated incidence patterns, nonuniform member sizes, and empty
  incidence classes.
- Preserve blocker minimality and both orientations of mutual-blocker equality.
- Do not promote the G4.5, G4.6, or G4.7 candidate into `claims.yaml` or
  `status.md` in this discovery gate.
- Do not infer novelty, priority, exact `sat(7)`, or exact `m(3,3)`.
- Do not publish, push, contact experts, or start a second mathematical
  objective in this gate.
