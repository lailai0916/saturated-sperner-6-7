# G4.15 Lean statement crosswalk

## Natural target

Section 7 of the G4.12 proof excludes the middle-layer split $(5,11)$. The present gate
formalizes its degree-three branch only. Let $\mathcal D$ be a five-row clutter and let
$\mathcal E=B(\mathcal D)$ have eleven rows. Assume every row on both sides has size at least
three. If some point has $\mathcal D$-degree three, then this configuration is impossible.

The complementary branch in which every point has degree at most two remains outside Lean. Its
natural proof invokes the frozen G4.10--G4.11 support-multigraph lower bound of fifteen blockers.

## Formal objects

| Natural object | Lean declaration |
|:---|:---|
| finite row | `AiMathLab.P0054.G413.Row` |
| finite row family | `AiMathLab.P0054.G413.Hypergraph` |
| clutter | `AiMathLab.P0054.G413.IsClutter` |
| blocker | `AiMathLab.P0054.G413.blocker` |
| point degree | `AiMathLab.P0054.G413.degree` |
| residual contraction | `AiMathLab.P0054.G413.residual` |

The exact formal theorem is `AiMathLab.P0054.G415.fiveEleven_degreeThree_impossible`. It is
quantified over an arbitrary finite ground set and assumes:

- `IsClutter H`;
- `H.card = 5`;
- `RowsCardAtLeast H 3`;
- `RowsCardAtLeast (blocker H) 3`;
- `(blocker H).card = 11`;
- `degree H x = 3` for some point `x`.

Its conclusion is `False`.

## Proof crosswalk

| Natural step | Lean declaration or proof block |
|:---|:---|
| the two rows avoiding $x$ are disjoint | `degreeThree_blockers_containing_card_ge_nine` |
| the choices $(p,q)$ give at least nine distinct blockers containing $x$ | `degreeThree_blockers_containing_card_ge_nine` |
| blockers avoiding $x$ are the blocker of the residual clutter | `blocker_residual` |
| the residual has at least two blockers | `blocker_card_ge_two_of_rows_cardAtLeast_two` |
| equality leaves exactly two residual blockers | blocker degree partition via `card_avoidPoint_add_degree` |
| the blocker of two rows has at least their cardinality product | `twoRow_blocker_card_ge_product` |
| the residual has at most five rows | `residual_card_le` |

## Boundary

This theorem does not exclude the degree-at-most-two branch, the full $(5,11)$ split, any other
G4.12 split, or every 54-member family. It strengthens the local Lean trust chain only and does not
assign the global theorem `sat(7)=55` the `FORMALIZED` label.
