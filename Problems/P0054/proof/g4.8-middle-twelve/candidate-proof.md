# P0054 G4.8 candidate: the middle layer has at least thirteen members

```text
CURRENT_GATE: P0054_G4_8_MIDDLE_LAYER_TOTAL_TWELVE
LOCAL_TARGET: m(3,3) >= 13
CANDIDATE_CONCLUSION: sat(7) >= 51
STATUS: PROVED_CANDIDATE_PENDING_REFEREE
```

## 1. Statement and reduction

`PROVED` relative to the frozen G4--G4.7 inputs: let `S` and `C` be finite
clutters on an arbitrary finite ground set such that

```text
S = B(C),
C = B(S),
|E| >= 3 for every E in S union C.
```

Then

```text
|S| + |C| >= 13.                                             (1.1)
```

The accepted G4.7 proof gives the lower bound twelve. If equality held, put
`a=|S|`, `b=|C|`, and exchange the sides so that `a<=b`. The only remaining
splits are

```text
(a,b) in {(5,7),(6,6)}.                                      (1.2)
```

Sections 3 and 4 exclude these two cases separately.

## 2. Three-row lemma at transversal number two

### Lemma 2.1

`PROVED`: if `H={A,B,C}` is a three-member clutter, every member has size at
least three, and `tau(H)>=2`, then

```text
|B(H)| >= 7.                                                  (2.1)
```

### Proof

There is no point common to all three rows. Suppose first that, say,
`X=A intersect B` has at least three points. For every `x in X` and `c in C`,
the pair `{x,c}` is a distinct minimal transversal. This gives at least nine.

If `|X|=2`, the same construction gives six blockers. Since `H` is a clutter,
both `A\B` and `B\A` are nonempty. If some choice of one point from each
difference meets `C`, that pair is a seventh blocker. Otherwise both
differences avoid `C`. The triple intersection is empty, so `C` is then
disjoint from `A union B`. Adjoining any point of `C` to such a choice gives a
seventh minimal transversal.

It remains that every pairwise intersection has size at most one. Put

```text
x=|A intersect B|, y=|A intersect C|, z=|B intersect C|,
p=|A\(B union C)|, q=|B\(A union C)|, r=|C\(A union B)|.
```

Here `x,y,z` are zero or one. The following distinct minimal transversals give
the lower bound

```text
xy+xz+yz+xr+yq+zp+pqr.                                      (2.2)
```

They are respectively pairs from two different pairwise-intersection classes,
a pairwise-intersection point with a private point of the missing row, and
triples containing one private point from every row.

If zero, one, two, or three of `x,y,z` equal one, the row-size constraints make
the expression in (2.2) at least, respectively,

```text
27, 15, 9, 7.
```

For example, in the last case `p,q,r>=1`, so (2.2) is
`3+p+q+r+pqr>=7`. This proves (2.1). `\square`

## 3. Five-member strengthening

### Lemma 3.1

`PROVED`: if `H={E_1,...,E_5}` is a finite clutter, every member has size at
least three, and `tau(H)>=3`, then

```text
|B(H)| >= 8.                                                  (3.1)
```

### Proof

The accepted G4.7 proof already gives at least nine blockers when a point has
incidence degree three, when the loop-multigraph support graph has matching
number zero or one, or when its actual two-edge matching is unique. It remains
to sharpen the cases with two distinct actual matchings.

Assume every point belongs to at most two rows. Fix actual two-edge matchings
`M` and `N` sharing an actual point. For each matching, adjoining any point
incident with its unmatched support vertex gives at least three minimal
three-point edge covers; denote the two generated blocker families by `F_M`
and `F_N`. Write

```text
M={e,f}, N={e,g}.
```

If `f` and `g` are parallel actual points, the generated families are disjoint
and give at least six blockers. Otherwise they intersect in at most the one
blocker `{e,f,g}` and give at least five.

The residual family `H-{e}` has at least three minimal transversals. It has at
least two by the accepted G4.7 residual-family lemma. If it had exactly two,
say `T_1,T_2`, both would be blockers of `H` of size at least three. The clutter
of minimal residual rows would be `B({T_1,T_2})`. An intersection of `T_1` and
`T_2` would create a singleton residual row; if they were disjoint, their
blocker would contain at least `|T_1||T_2|>=9` two-point rows. Both alternatives
contradict the five residual rows, each of size at least two.

These at least three blockers avoid `e` and are outside both generated
families. The parallel case therefore gives at least nine blockers, and the
remaining case gives at least eight.

It remains that no two actual matchings share an actual point. Fix an actual
matching `M` and let `w` be its unmatched support vertex. Every point incident
with `w` is then a loop. Indeed, a nonloop from `w` to an endpoint of one edge
of `M` would be disjoint from the other edge and create a new matching sharing
that other actual point with `M`.

The row at `w` is therefore a disjoint component containing at least three
loops. The other four rows form a clutter `K` whose rows still have size at
least three. Blocker involution and the private-witness injection give
`|B(K)|>=3`. Component factorization now gives

```text
|B(H)|=|E_w| |B(K)|>=3*3=9.
```

This proves (3.1). `\square`

## 4. Six-member lemma

### Lemma 4.1

`PROVED`: if `H={E_1,...,E_6}` is a finite clutter, every member has size at
least three, and `tau(H)>=3`, then

```text
|B(H)| >= 7.                                                  (4.1)
```

### Proof: high-incidence points

A point in six rows is a one-point transversal, and a point in five rows can
be extended to a transversal of size at most two. Both are impossible.

If a point `x` belongs to exactly four rows, the remaining two rows must be
disjoint. Choosing one point from each of them and adjoining `x` gives at least
`3*3=9` three-point transversals. The two chosen points have the remaining
rows as private witnesses, and `x` is indispensable because `tau(H)>=3`.
Hence all of these transversals are minimal.

Suppose `x` belongs to exactly three rows, and let `K` be the other three rows.
Then `tau(K)>=2`; otherwise `x` and a common point of `K` would form a
two-point transversal of `H`. Lemma 2.1 gives at least seven members of
`B(K)`. For each `T in B(K)`, use `T` itself if it hits all six rows, and use
`T union {x}` otherwise. In the first case the private rows certifying
minimality in `K` also certify minimality in `H`. In the second case `x` has a
missed row as a private witness, while every point of `T` retains its private
row in `K`. This is an injection from `B(K)` into `B(H)`.

Consequently a counterexample to (4.1) would have every active point in at
most two rows. Represent the points as actual loops and nonloop edges on the
six row indices, retaining parallel actual points. Minimal transversals are
minimal edge covers, and every support vertex has actual incidence degree at
least three.

### Proof: matching number at most two

If the simple nonloop support graph has matching number zero, independent loop
choices give at least `3^6` blockers.

If its matching number is one, fix an actual matching edge. The other four
support vertices are pairwise nonadjacent. Choose one incident actual point at
each of them. Those four selected points have distinct private unmatched
vertices; minimizing the resulting cover can only discard the fixed edge.
Different choices remain distinct, giving at least `3^4` blockers.

If the matching number is two, fix an actual two-edge matching with unmatched
vertices `u,v`. There is no edge between `u` and `v`, or the matching would
extend. For every choice of an actual point incident with `u` and one incident
with `v`, minimize their union with the fixed matching. The two chosen points
remain through minimization because `u` and `v` are private. Different pairs
give distinct blockers, so there are at least

```text
d(u)d(v)>=3*3=9.
```

### Proof: perfect matching

It remains that the support graph has an actual perfect matching

```text
M={e_1,e_2,e_3}.
```

Assume for contradiction that `|B(H)|<=6`. Delete the three matching points
from every row. Each residual row has size at least two. Let `R` be the clutter
of inclusion-minimal residual rows and let `T=B(R)`. The members of `T` are
exactly the blockers of `H` avoiding all three matching points, and every one
has size at least three because `tau(H)>=3`.

We claim `|T|>=4`. One member would make `R` a family of singleton rows. Two
members either intersect and again create a singleton row, or are disjoint and
create at least `3*3=9` two-point rows. If `|T|=3`, Lemma 2.1 applies to `T`:
its rows have size at least three and `tau(T)>=2` because every member of
`R=B(T)` has size at least two. It would give `|R|>=7`, although `R` has at
most six members.

Since `M` itself is a blocker, `|T|` is four or five. Put `C=B(H)`, so
`H=B(C)`.

If `|T|=5`, the bound `|C|<=6` makes `C` consist exactly of `M` and the five
rows in `T`. The row `M` is disjoint from all five. Component factorization
gives

```text
6=|H|=|M| |B(C\{M})|=3 |B(C\{M})|.
```

Thus the other five-row clutter would have only two blockers, and blocker
involution would force each of its rows to have size at most two, a
contradiction.

Suppose `|T|=4`. If no other blocker of `H` used a point of `M`, the same
factorization with four remaining rows would again give exactly two blockers
for that four-row clutter, contradicting its row sizes.
Hence, under `|B(H)|<=6`, there is exactly one further blocker `N` meeting
`M`. Put

```text
I=N intersect M.
```

The blocker clutter makes `|I|` equal to one or two: it is nonempty, while
`|I|=3` would make `M` a subset of `N`. Let `D` be the four rows of `C` that
avoid `M`.

For every `e in I` and every `Q in B(D)`, the set `Q union {e}` is a minimal
transversal of `C`: the point `e` covers `M` and `N`, while `Q` covers `D`.
The row `M` is private for `e`, and the private rows of the points of `Q` lie
in `D`, so minimality is preserved. The four-row clutter `D` has at least
three blockers, since at most two blockers would force every row of `D` to
have size at most two.

For every `e in M\I`, apply the accepted G4.7 residual-family lemma to
`C\{M}` after deleting all points of `I`. Every row of `C\{M}` has size at
least three. If `|I|=1`, the lemma supplies at least two minimal transversals;
if `|I|=2`, it supplies at least one. These transversals avoid `M`, because
the residual rows do. Adjoining `e` gives distinct minimal transversals of
`C`: `M` is private for `e`, and all other private rows are retained. Their
unique point in `M` is `e`.

Therefore `B(C)=H` has at least

```text
3+2*2=7  if |I|=1,
2*3+1=7  if |I|=2.
```

This contradicts `|H|=6` and proves (4.1). `\square`

## 5. Local and global deductions

Assume the mutual-blocker pair in (1.1) has total size at most twelve and
exchange its sides so that `a<=b`. The private-witness bounds give `a>=3`.

- If `a=3`, the accepted three-member lemma gives `b>=27`.
- If `a=4`, the accepted four-member lemma gives `b>=9`.
- If `a=5`, Lemma 3.1 gives `b>=8`.
- If `a=6`, Lemma 4.1 gives `b>=7`.

Every case contradicts `a+b<=12`, proving (1.1). Applying it to the accepted
middle-layer interface gives

```text
|A_3|>=13,
|F|>=1+6+12+13+12+6+1=51.                                  (5.1)
```

Thus the frozen eventual-stability reduction gives the candidate consequence
`sat(7)>=51`.

## 6. Computation and evidence boundary

`COMPUTED`: the frozen G4.6 search exhausts only `(5,5)` and `(5,6)`. It is not
a dependency of the new `(5,7)` or `(6,6)` exclusions.

`UNKNOWN`: exact `m(3,3)`, exact `sat(7)`, existence or compatibility of a
thirteen-member middle layer, novelty, and priority.

No claim or status file is modified by this candidate.
