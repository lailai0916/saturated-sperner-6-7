# G4.13 Lean statement crosswalk

> Historical checkpoint note (updated 2026-07-30): this file records the
> local G4.13 theorem at the time it was first isolated.  The current
> exact-value dependency graph uses it through
> `MiddleSevenEightFiveKernelBranch.sevenRows_degreeTwo_impossible` in the
> total-fifteen `(7,8)` branch; the total-sixteen `(8,8)` branch is closed by
> `G420.eightEight_impossible`.  See `formalization-report.md` for the current
> global status.

## Natural target

The G4.13 natural-language theorem excludes an admissible eight-row completion of the five-row
degree-three kernel. It is quantified over an arbitrary finite ground set and permits inactive
points, parallel incidence supports, and nonuniform row sizes.

## Formal objects

| Natural object | Lean declaration |
|:---|:---|
| row | `AiMathLab.P0054.G413.Row` |
| finite row family | `AiMathLab.P0054.G413.Hypergraph` |
| transversal | `AiMathLab.P0054.G413.IsTransversal` |
| blocker | `AiMathLab.P0054.G413.blocker` |
| clutter | `AiMathLab.P0054.G413.IsClutter` |
| residual contraction | `AiMathLab.P0054.G413.residual` |
| forced completion base | `AiMathLab.P0054.G413.forcedBase` |
| admissible kernel completion | `AiMathLab.P0054.G413.IsKernelCompletion` |

`IsKernelCompletion K x D` records that `D` is an eight-row clutter with minimum row size three
and maximum point degree three, that `K` has maximum point degree three, that `D` contains the
forced lift of `B(K)`, and that every row of `K` is a blocker of `D`. These are the interfaces used
by the natural completion argument.

## Kernel theorem status

`no_kernel_completion_of_locked_dependencies` proves the final 3–5, 6–7, and 8 blocker case
assembly. It retains residual Lemma 2 and the pair-endpoint property for the 6- and 7-row cases as
hypotheses. The 8-row case is unconditional.

`no_kernel_completion_of_four_five_endpoint_eight` refines the first dependency. Its three-row
Residual Lemma 2 branch is unconditional; only the four- and five-row branches remain hypotheses.

`no_kernel_completion_of_four_pair_five_endpoint_eight` refines it again. Four-row residuals whose
rows all have size at least three are now unconditional with the stronger blocker lower bound nine.
Only the pair-containing four-row branch and the five-row branch remain hypotheses.

`no_kernel_completion_of_five_endpoint_eight` closes the remaining four-row branch. The
pair-containing case is proved by two disjoint residual-blocker injections and the three possible
numbers of rows avoiding both pair endpoints. The only remaining Residual Lemma 2 hypothesis is the
five-row branch.

`no_kernel_completion_of_five_large_endpoint_eight` closes every pair-containing five-row branch.
The proof classifies the number of rows avoiding both endpoints of a chosen pair and handles all
cases from one through four. The only remaining Residual Lemma 2 hypothesis is a five-row clutter
whose rows all have size at least three.

`fiveRow_large_residual_bound` closes that all-large branch. If a row has size three, contraction at
one of its points reduces to the already formalized three-, four-, or five-row pair case. Otherwise
both the clutter and its blocker have minimum row size four, and an explicit product injection gives
at least sixteen blockers. Consequently `residualLemma2` is unconditional, and
`no_kernel_completion_of_endpoint_eight` retains only the pair-endpoint property.

`kernelCompletion_pair_endpoint` derives that property from an actual completion in the 6- and
7-row cases. `no_kernel_completion_of_eight` combines it with the unconditional residual and
8-row results. This is the unconditional formal G4.13 local no-completion theorem.

## Unconditional results

The current modules prove blocker involution, both residual blocker identities, private-row
witnesses, exact one- and two-row blocker formulas, the forced-base completion lemma, and the
`K3` incidence contradiction without adding mathematical hypotheses. They also prove the exact
three-row equality case: if a three-row clutter and its blocker both have three rows and both sides
have minimum row size two, then all three original rows are pairs. If every blocker row instead has
size at least three, the original rows are pairwise disjoint and have at least eight blockers. A
four-row clutter with minimum row size three and blocker minimum row size three has at least nine
blockers, by the isolated-component or three-leaf-star split. A four-row clutter with minimum row
size two, at most three pair rows, and blocker minimum row size three has at least six blockers,
including the pair-containing case. A five-row clutter under the same residual hypotheses also has
at least six blockers in all cases.

All five pair-graph branches are unconditional. `p4_pairGraph_impossible` and
`p3k2_pairGraph_impossible` formalize the path branches. `threeK2_pairGraph_impossible` combines the
finite support classification with an arbitrary-ground-set lifting and persistence argument. The
existing `K3` and `K1,3` theorems close the remaining shapes. Their exhaustive assembly is
`fiveRow_eight_blocker_impossible`.

## Historical global boundary

No declaration defines the eventual stable number `sat(7)`, excludes every 54-member family, or
connects all G4.12 branches to the existing `Fin 11` construction. The Lean work in this checkpoint
does not prove `sat(7)=55`.

That boundary was later closed.  As revalidated on 2026-07-30, the exported
theorem `Sat7StableExact.sat_seven_eq_fifty_five` has type
`IsStableSaturationNumber 7 55` and includes every required branch in its
dependency graph.
