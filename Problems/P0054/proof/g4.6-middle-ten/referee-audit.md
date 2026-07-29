# P0054 G4.6 referee audit

```text
CURRENT_GATE: P0054_G4_6_MIDDLE_LAYER_TOTAL_TEN
REVIEWED_COMMIT: 5ef8ab5
VERDICT: ACCEPT
SCOPE: arbitrary finite trace ground set U
NETWORK: OFFLINE
```

## 1. Verdict

`PROVED`: the candidate's deduction from the frozen G4--G4.5 inputs is sound:

```text
m(3,3) >= 11,
|A_3| >= 11,
|F| >= 1+6+12+11+12+6+1 = 49.
```

Thus a middle layer of total size ten is impossible. This audit does not
promote a claims entry or determine exact `m(3,3)` or exact `sat(7)`.

The frozen G4.4 and G4.5 candidate proofs, the G4.5 Referee report, the G4.5
post-validation record, and the G4.3 incidence engine all match the hashes in
`frozen-subproblem.md`.

## 2. Four-member lemma

`PROVED`: the intersection graph of four rows has matching number at most one,
because two vertex-disjoint graph edges give a transversal of size at most two.
The cases with at least two isolated rows, exactly one isolated row, and no
isolated row exhaust all such graphs.

Two isolated rows give at least `3*3=9` blockers by component factorization. In
the one-isolate case, finite blocker involution on the remaining three-row
clutter forces at least three blockers, so factorization again gives at least
nine. With no isolate the graph is a three-leaf star; fixing one center--leaf
intersection and choosing one point from each other leaf gives nine distinct
minimal three-point transversals.

## 3. Five-member lemma

`PROVED`: a point in at least four rows would give a transversal of size at
most two. A point in exactly three rows forces the remaining two rows to be
disjoint and gives at least nine minimal three-point transversals.

When every point has incidence degree at most two, the loop-multigraph model
preserves actual points, including parallel points with the same support. The
matching-number cases `nu=0`, `nu=1`, and `nu=2` are exhaustive.

- For `nu=0`, independent loop choices give at least `3^5` blockers.
- For `nu=1`, the simple support graph is a star or a triangle with isolated
  vertices. The displayed constructions give at least `27` or `9` blockers.
- For `nu=2`, every fixed actual two-edge matching gives at least three
  minimal edge covers. A second actual matching is handled whether it is
  disjoint, shares one actual point with parallel remaining edges, or shares
  one actual point with different remaining supports. In the sole five-cover
  overlap case, an inclusion-minimal subcover avoiding the shared point gives
  a sixth blocker.
- If the actual matching is unique, every point at the unmatched support
  vertex is a loop. The candidate's replacement construction gives three
  blockers avoiding one fixed matching edge, disjoint from the three blockers
  containing that edge.

These arguments retain loops, repeated supports, inactive ground points,
nonuniform row sizes, and arbitrary finite ground sets. Minimality follows
from the transversal-number hypothesis or from an explicit private support
vertex in every constructed cover.

## 4. Local and global deduction

For a mutual-blocker pair, the private-witness injection gives at least three
members on both sides and transversal number at least three in both
orientations. If `a+b<=10` and `a<=b`, then `a` is `3`, `4`, or `5`. The
three-, four-, and five-member lemmas give respectively

```text
b >= 27, b >= 9, b >= 6,
```

contradicting every possible split. Hence `m(3,3)>=11`.

The accepted G4.5 interface identifies the middle layer with such a
mutual-blocker pair on the same finite trace ground set. Adding the frozen
other-layer bounds gives the candidate global consequence `sat(7)>=49`.

## 5. Evidence boundary

`COMPUTED`: the companion incidence-pattern search reports no `(5,5)` or
`(5,6)` pair and passed its two semantic blocker validators. The computation
is regression evidence only and is not a dependency of the arbitrary-finite
proof.

`UNKNOWN`: exact `m(3,3)`, exact `sat(7)`, novelty, and priority.

```text
FIRST_INVALID_STEP: NONE
MATHEMATICAL_VERDICT: ACCEPT
CLAIMS_OR_STATUS_MODIFIED: NO
```
