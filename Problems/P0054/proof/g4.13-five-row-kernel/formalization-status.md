# P0054 G4.13 formalization status

```text
G413_NATURAL_LANGUAGE: PROVED_CANDIDATE
G413_ADVERSARIAL_REVIEW: ACCEPT_SAME_AGENT
G413_LEAN_FOUNDATION: FORMALIZED
G413_LEAN_LOCAL_THEOREM: FORMALIZED
G412_EXACT_VALUE_LEAN: NOT_YET_FORMALIZED
FORMAL_REPOSITORY_BOUNDS: 47 <= sat(7) <= 55
CLAIM_OR_STATUS_PROMOTION: NOT_AUTHORIZED_BY_CURRENT_EVIDENCE
```

## Frozen source

The files copied into this directory preserve the repaired G4.13 proof artifacts byte for byte.
Their binding hashes remain those in `p0054_g413_dependency_manifest_v1.md`.

The inaccurate temporary file `p0054_g413_stage_1_10_completion_v1.md` is deliberately excluded.
It reported stage 10 as complete before any G4.13 Lean module existed.

## Lean checkpoint

The following modules have passed their individual Lake targets:

- `AiMathLab.P0054G413.ClutterBasic`;
- `AiMathLab.P0054G413.BlockerInvolution`;
- `AiMathLab.P0054G413.Residual`;
- `AiMathLab.P0054G413.SmallRows`;
- `AiMathLab.P0054G413.ThreeRows`;
- `AiMathLab.P0054G413.FourRows`;
- `AiMathLab.P0054G413.FourRowPair`;
- `AiMathLab.P0054G413.FiveRowPair`;
- `AiMathLab.P0054G413.FiveRowLarge`;
- `AiMathLab.P0054G413.ResidualBounds`;
- `AiMathLab.P0054G413.PairEndpoint`;
- `AiMathLab.P0054G413.PairGraphs.Remaining`;
- `AiMathLab.P0054G413.PairGraphs.Support`;
- `AiMathLab.P0054G413.PairGraphs.Shapes`;
- `AiMathLab.P0054G413.PairGraphs.Trace`;
- `AiMathLab.P0054G413.PairGraphs.Restriction`;
- `AiMathLab.P0054G413.PairGraphs.P4`;
- `AiMathLab.P0054G413.PairGraphs.P3K2`;
- `AiMathLab.P0054G413.PairGraphs.ThreeK2`;
- `AiMathLab.P0054G413.PairGraphs.ThreeK2Lift`;
- `AiMathLab.P0054G413.PairGraphs.Eight`;
- `AiMathLab.P0054G413.FiveRowKernel`.

They formalize finite hypergraphs, clutters, minimal transversals, blocker involution,
private-row witnesses, the private-row cardinality bound, minimization, deletion,
contraction, both deletion-contraction blocker identities, exact one- and two-row blocker
formulas, all five pair-graph contradictions, the forced base, the completion lemma,
the exact three-row equality case, the pairwise-disjoint three-row bound of eight, the four-large-row
bound of nine, the pair-containing four-row residual bound of six, and the unconditional local
kernel no-completion theorem. They also formalize every five-row residual case, including the
pair-row equality cases and the all-large case.

Residual Lemma 2, the pair-endpoint application to an actual completion, and all five 8-row
pair-graph branches are unconditional. `no_kernel_completion_of_eight` combines them without a
residual, endpoint, or eight-row impossibility hypothesis.

## Remaining Lean gaps

- the other G4.12 branches and the global canonical reduction.

G4.13's local no-completion statement has the `FORMALIZED` label. Until the remaining global gaps
close, `sat(7)=55` does not.
