# G4.13 local formalization report

> Historical checkpoint note (updated 2026-07-30): the status block below
> describes the moment the local theorem first closed.  The complete stable
> exact value subsequently closed and was revalidated on 2026-07-30; see
> `formalization-report.md`.  In the current dependency graph this local
> theorem is used in the total-fifteen `(7,8)` branch, while
> `G420.eightEight_impossible` closes `(8,8)`.

```text
STATUS: FORMALIZED_LOCAL_THEOREM
G413_LOCAL_THEOREM: FORMALIZED
GLOBAL_EXACT_VALUE: OPEN
PROOF_PLACEHOLDERS: NONE
```

## Compiled modules

- `AiMathLab/P0054G413/ClutterBasic.lean`;
- `AiMathLab/P0054G413/BlockerInvolution.lean`;
- `AiMathLab/P0054G413/Residual.lean`;
- `AiMathLab/P0054G413/SmallRows.lean`;
- `AiMathLab/P0054G413/ThreeRows.lean`;
- `AiMathLab/P0054G413/FourRows.lean`;
- `AiMathLab/P0054G413/FourRowPair.lean`;
- `AiMathLab/P0054G413/FiveRowPair.lean`;
- `AiMathLab/P0054G413/FiveRowLarge.lean`;
- `AiMathLab/P0054G413/ResidualBounds.lean`;
- `AiMathLab/P0054G413/PairEndpoint.lean`;
- `AiMathLab/P0054G413/PairGraphs/Remaining.lean`;
- `AiMathLab/P0054G413/PairGraphs/Support.lean`;
- `AiMathLab/P0054G413/PairGraphs/Shapes.lean`;
- `AiMathLab/P0054G413/PairGraphs/Trace.lean`;
- `AiMathLab/P0054G413/PairGraphs/Restriction.lean`;
- `AiMathLab/P0054G413/PairGraphs/P4.lean`;
- `AiMathLab/P0054G413/PairGraphs/P3K2.lean`;
- `AiMathLab/P0054G413/PairGraphs/ThreeK2.lean`;
- `AiMathLab/P0054G413/PairGraphs/ThreeK2Lift.lean`;
- `AiMathLab/P0054G413/PairGraphs/Eight.lean`;
- `AiMathLab/P0054G413/FiveRowKernel.lean`;
- `AiMathLab/P0054G413.lean`.

The audit entry is `Problems/P0054/formal/G413.lean`. It checks the public declarations and prints
their axiom dependencies.

## Evidence label

`no_kernel_completion_of_eight` has the `FORMALIZED` label for the exact local G4.13 statement. It
quantifies over an arbitrary finite ground set and assumes only the five-row degree-three kernel,
the three pair blockers, the blocker-size upper bound, and the formal completion interface.

Residual Lemma 2 is unconditional. The 6- and 7-row endpoint property is derived from an actual
completion. The 8-row branch classifies the three pair rows into `P4`, `P3+K2`, `3K2`, `K3`, and
`K1,3`, then excludes every shape. No proof placeholder, new axiom, `sorry`, `admit`, `unsafe`,
`native_decide`, or `run_tac` is used.

At this historical checkpoint, the local theorem did not formalize the other
G4.12 branches or the global canonical reduction and therefore did not yet
give `sat(7)=55` the `FORMALIZED` label.  Those dependencies are now closed by
the final stable-exact development.
