# P0054 G4.13 3K2 and remaining graphs Referee v1

```text
VERDICT: ACCEPT_AFTER_3K2_PERSISTENCE_REPAIR
FIRST_INVALID_STEP_IN_3K2_V3: POINTWISE_RESTORATION_WITHOUT_PERSISTENCE
FIRST_INVALID_STEP_IN_3K2_V4: NONE
REVIEWED_3K2: p0054_g413_3k2_pure_projection_v4.md
REVIEWED_K3_K13: p0054_g413_remaining_pair_graphs_v2.md
STATUS: PROVED_CANDIDATE
NETWORK: MATHEMATICS_OFFLINE
FORMAL_PROMOTION: NO
```

## 3K2 classification

Each fixed pair has support type `D` or `I`.

If at least one pair has type `I`, all type-`I` pairs share one common row.
Deleting that row leaves three pairwise orthogonal $2+2$ partitions of four
rows. The number of type-`I` pairs gives exactly three projection classes.

If all pairs have type `D`, the projected rows are vertices of the cube
$\{0,1\}^3$. Every two-coordinate projection is complete, so the missing
vertices form an independent set. Its size gives exactly two classes: the
duplicated parity class and the asymmetric class.

Thus the five-class classification is exhaustive.

## Four saturated classes

The three type-`I` classes and the duplicated all-`D` class have seven
endpoint-only blockers. Every endpoint already has degree three.

For each class, one projected row $R$ and one two-endpoint set $Q$ satisfy:

$$
Q\cap R=\varnothing
$$

while $Q$ meets every other projected row. The endpoint-free eighth blocker
meets the full row $R$ at an outside point $z$. Minimizing $Q\cup\{z\}$
preserves $z$ and at least one saturated endpoint. This violates the degree
bound.

## Asymmetric all-D repair

Version 3 tested an outside point in isolation but did not justify that the
resulting blocker survives when other outside points are present.

Version 4 adds the required persistence lemma. Restrict the full clutter to
the six endpoints and one outside point $x$. The five distinct endpoint rows
keep the restriction a clutter. Any blocker of the restriction has private
rows, and restoring omitted points does not change their intersection with
the selected blocker. The blocker therefore persists in the full clutter.

Pointwise support elimination now becomes valid. Every outside support except
$\{R_4\}$ immediately raises a saturated endpoint degree or creates an extra
pair. One $\{R_4\}$ point gives only seven blockers. Two such points produce
two persistent blockers through $A,C,E$ and raise all three degrees to four.

The asymmetric class is impossible.

## Triangle

In the `K3` pair graph, every one of the five dual rows contains at least two
triangle endpoints. The total endpoint incidence is at least ten. The
degree-three bound gives at most nine. This is a direct contradiction.

## Three-leaf star

In the `K1,3` graph, the center already has degree three in the eight-row
family. Delete it from the five dual rows and minimize. The residual has
between three and five rows, minimum row size two, at most three pair rows,
and transversal number at least three.

Residual Lemma 2 in `p0054_g413_residual_lemmas_v3.md` gives at least six
blockers. Residual blocker identity gives exactly the five original rows that
avoid the center. This contradiction excludes the star.

## Verdict

`FIRST_INVALID_STEP_IN_3K2_V4: NONE`.

The 3K2, K3, and K1,3 branches reach `PROVED_CANDIDATE`. Old projection and
support tables remain `COMPUTED` cross-checks only.

