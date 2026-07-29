# P0054 G4.9 middle-layer total-thirteen problem

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_9_MIDDLE_LAYER_TOTAL_THIRTEEN
BASE_COMMIT: abcff7782bee1991cbf72a6e9a9798d472e4e4ab
OFFICIAL_GLOBAL_BOUNDS: 47 <= sat(7) <= 55
INTERNAL_REFEREE_ACCEPTED_CANDIDATE: sat(7) >= 51
TARGET_IF_PROVED: sat(7) >= 52
NETWORK: MATHEMATICS_OFFLINE
```

## Frozen inputs

The following files are immutable inputs for this gate:

| Path | SHA-256 |
|---|---|
| `Problems/P0054/proof/g4.6-middle-ten/candidate-proof.md` | `bebe22bea1bf9021ec02a6e60ebbe2b2499de2bf15bea0769c24ea66c2d70c15` |
| `Problems/P0054/proof/g4.8-middle-twelve/frozen-subproblem.md` | `733cf2f3b847e55ec3ab766b5b2689721211b89a19abdd323a025934cd0d9e87` |
| `Problems/P0054/proof/g4.8-middle-twelve/candidate-proof.md` | `5bb6f43906a9048cd87a861569d4ed729ab6a2f83bf334943344b1c55dbd09e0` |
| `Problems/P0054/proof/g4.8-middle-twelve/referee-audit.md` | `f71c8df9bf99c6c2127365906d392d8466da70430ab73728080d464ba0ccf4c4` |
| `Problems/P0054/proof/g4.8-middle-twelve/post-referee-validation.md` | `212f3ff905ac8b0edb22ced36f8daeb20d8d555d5811a558e7c9813467f77521` |

`PROVED`: the accepted G4.8 candidate recognizes the two sides of the middle
layer as finite mutual blockers. Every member on both sides has size at least
three, and their total cardinality is at least thirteen.

`PROVED`: the frozen other-layer bounds are

```text
(|A_0|,|A_1|,|A_2|,|A_4|,|A_5|,|A_6|) >= (1,6,12,12,6,1).
```

The G4.8 result has an isolated Referee `ACCEPT` verdict and complete host
validation. G4.5--G4.8 have not been promoted into `claims.yaml` or
`status.md` because human review remains pending.

## One objective

Determine whether every finite mutual-blocker pair whose members have size at
least three has total cardinality at least fourteen. By the accepted G4.8
lemmas, a total-thirteen counterexample must have side sizes `(4,9)`, `(5,8)`,
or `(6,7)`, up to exchange.

A concrete admissible pair in any one split refutes the target. A negative
incidence-pattern search remains `COMPUTED` unless accompanied by a complete
arbitrary-finite combinatorial proof.

## Evidence boundary

- Allow arbitrary finite ground sets, inactive points, loops, parallel actual
  points, repeated incidence patterns, nonuniform member sizes, and empty
  incidence classes.
- Preserve blocker minimality and both orientations of mutual-blocker equality.
- Treat `(4,9)`, `(5,8)`, and `(6,7)` as separate obligations. Do not combine
  partial arguments into a proof of the total-thirteen exclusion.
- Do not promote G4.5--G4.9 into `claims.yaml` or `status.md` in this discovery
  gate.
- Do not infer novelty, priority, exact `sat(7)`, or exact `m(3,3)`.
- Do not publish, push, contact experts, or start a second mathematical
  objective in this gate.
