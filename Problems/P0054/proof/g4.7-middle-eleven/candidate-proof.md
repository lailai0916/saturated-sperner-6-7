# P0054 G4.7 candidate: the middle layer has at least twelve members

```text
CURRENT_GATE: P0054_G4_7_MIDDLE_LAYER_TOTAL_ELEVEN
LOCAL_TARGET: m(3,3) >= 12
CANDIDATE_CONCLUSION: sat(7) >= 50
STATUS: PROVED_CANDIDATE_PENDING_REFEREE
```

## 1. Statement and reduction

`PROVED` relative to the frozen G4--G4.6 inputs: let `S` and `C` be finite
clutters on an arbitrary finite ground set such that

```text
S = B(C),
C = B(S),
|E| >= 3 for every E in S union C.
```

Then

```text
|S| + |C| >= 12.                                             (1.1)
```

The accepted G4.6 proof gives the lower bound eleven. If equality held, put
`a=|S|`, `b=|C|`, and exchange the two sides so that `a<=b`. The G4.6
three- and four-member lemmas give respectively `b>=27` when `a=3` and
`b>=9` when `a=4`. The only remaining split is therefore

```text
(a,b)=(5,6).                                                  (1.2)
```

It suffices to strengthen the G4.6 five-member blocker lemma from six to
seven.

## 2. Residual-family lemma

For a finite family `H` and a set `D` of ground points, write

```text
H-D={E\D:E in H}.
```

### Lemma 2.1

`PROVED`: let `H` be a nonempty finite family whose every member has size at
least three.

1. If `|D|<=2`, then `H-D` has a minimal transversal. Every such transversal
   is also a member of `B(H)` and avoids `D`.
2. If `D={e}`, then `H-D` has at least two minimal transversals.

### Proof

For the first assertion, every residual row is nonempty. Choosing one point
from each row gives a transversal, and finiteness supplies an
inclusion-minimal one `T`. Since `T` avoids `D`, a subset of `T` hits an
original row exactly when it hits the corresponding residual row. Thus `T`
is also minimal for `H`.

For the second assertion, every residual row has size at least two. Let `K` be
the clutter of inclusion-minimal residual rows; then `B(K)=B(H-D)`. If this
blocker had a unique member `T`, finite blocker involution would give

```text
K=B(B(K))=B({T})={{x}:x in T}.
```

This contradicts the fact that every member of `K` is a residual row of size
at least two. Hence `|B(H-D)|>=2`. `\square`

The lemma does not assume that `H-D` remains a clutter; passing to its
inclusion-minimal rows preserves exactly the same transversals.

## 3. Strengthened five-member lemma

### Lemma 3.1

`PROVED`: if `H={E_1,...,E_5}` is a finite clutter, every member has size at
least three, and `tau(H)>=3`, then

```text
|B(H)| >= 7.                                                  (3.1)
```

### Proof: reduction to the matching case

The high-incidence and low-matching cases follow the accepted G4.6 proof. A
point in at least four rows gives a transversal of size at most two. A point
in exactly three rows forces the remaining two rows to be disjoint and gives
at least `3*3=9` minimal transversals.

Assume every active point belongs to at most two rows. Represent actual points
as loops or nonloop edges on the five row indices, retaining parallel actual
points. Transversals of `H` are edge covers of the five support vertices. Each
support vertex has actual incidence degree

```text
d(i)=|E_i|>=3.                                                (3.2)
```

Let `J` be the simple support graph of nonloop points. If its matching number
is zero, independent loop choices give at least `3^5` minimal covers. If its
matching number is one, `J` is a star or a triangle with isolated vertices;
the G4.6 constructions give at least `27` or `9` minimal covers. It remains to
consider matching number two.

### Proof: two actual matchings

Fix an actual two-edge matching `M` and let `w_M` be its unmatched support
vertex. For every actual point `p` incident with `w_M`,

```text
M union {p}
```

is a minimal three-point edge cover. Denote these `d(w_M)>=3` blockers by
`F_M`.

Suppose there is a distinct actual two-edge matching `N`. If `M` and `N`
share no actual point, `F_M` and `F_N` are disjoint, because a three-point set
cannot contain four distinct matching points. Thus they give at least six
blockers. Choose `e in M` and `f in N`. Lemma 2.1 applied with `D={e,f}`
gives a blocker avoiding both points. It belongs to neither generated family,
so there are at least seven blockers.

Suppose instead that

```text
M={e,f}, N={e,g}.
```

If `f` and `g` are distinct parallel actual points, `F_M` and `F_N` are
disjoint and give at least six blockers. Otherwise their supports are
distinct two-subsets of the three vertices outside the support of `e`. The
two generated families intersect in at most the single blocker `{e,f,g}` and
therefore give at least five blockers.

Every generated blocker contains `e`. Lemma 2.1 applied with `D={e}` gives at
least two blockers avoiding `e`. They are outside both generated families, so
the parallel case gives at least eight blockers and the remaining case gives
at least seven.

### Proof: unique actual matching

Finally suppose `M` is the unique actual two-edge matching, with unmatched
support vertex `w`. Every actual point incident with `w` is a loop at `w`; a
nonloop from `w` to an endpoint of one matching edge would be disjoint from
the other matching edge.

Let `K` be the four-row clutter on the other support vertices. The active
ground points of `K` are disjoint from the at least three loops at `w`, and
every row of `K` still has size at least three. If `|B(K)|<=2`, blocker
involution and the private-witness injection, applied to
`K=B(B(K))`, would force every row of `K` to have size at most two. Hence

```text
|B(K)|>=3.
```

Blocker factorization over the two disjoint active components now gives

```text
|B(H)|=|E_w| |B(K)|>=3*3=9.
```

All matching cases prove (3.1). `\square`

## 4. Local and global deductions

Assume the mutual-blocker pair in (1.1) has total size at most eleven and
exchange its sides so that `a<=b`. The private-witness bounds give `a>=3`.

- If `a=3`, the three-member lemma gives `b>=27`.
- If `a=4`, the four-member lemma gives `b>=9`.
- If `a=5`, Lemma 3.1 gives `b>=7`.

Every case contradicts `a+b<=11`, proving (1.1). Applying it to the accepted
middle-layer interface gives

```text
|A_3|>=12,
|F|>=1+6+12+12+12+6+1=50.                                  (4.1)
```

Thus the frozen eventual-stability reduction gives the candidate consequence
`sat(7)>=50`.

## 5. Computation and evidence boundary

`COMPUTED`: the frozen G4.6 incidence-pattern search found no `(5,6)` pair.
That zero hit is regression evidence for Lemma 3.1, not a dependency of its
arbitrary-finite proof.

`UNKNOWN`: exact `m(3,3)`, exact `sat(7)`, existence or compatibility of a
twelve-member middle layer, novelty, and priority.

No claim or status file is modified by this candidate.
