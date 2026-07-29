# P0054 G4.6 candidate: the middle layer has at least eleven members

```text
CURRENT_GATE: P0054_G4_6_MIDDLE_LAYER_TOTAL_TEN
LOCAL_TARGET: m(3,3) >= 11
CANDIDATE_CONCLUSION: sat(7) >= 49
STATUS: PROVED_CANDIDATE_PENDING_REFEREE
```

## 1. Statement and dependencies

`PROVED` relative to the frozen G4--G4.5 inputs: let `S` and `C` be finite
clutters on an arbitrary finite ground set such that

```text
S = B(C),
C = B(S),
|E| >= 3 for every E in S union C.
```

Then

```text
|S| + |C| >= 11.                                             (1.1)
```

Applying (1.1) to the accepted middle-layer interface gives

```text
|A_3| >= 11,
|F| >= 1+6+12+11+12+6+1 = 49.                               (1.2)
```

The proof uses only finite blocker involution, the private-witness lemma, and
the elementary intersection arguments below. It does not use the bounded
search recorded with this gate.

## 2. Basic blocker facts

For a finite clutter `H`, write `B(H)` for its inclusion-minimal
transversals and `tau(H)` for the minimum transversal size.

`PROVED` (private witnesses): if `T in B(H)`, then every `x in T` has a
distinct witness `E_x in H` with `T intersect E_x={x}`. Consequently

```text
|T| <= |H|.                                                   (2.1)
```

`PROVED`: in a mutual-blocker pair satisfying the hypotheses of (1.1), put
`a=|S|` and `b=|C|`. Applying (2.1) in both directions gives

```text
a >= 3, b >= 3,
tau(S) >= 3, tau(C) >= 3.                                    (2.2)
```

The accepted G4.5 proof already contains the three-member lemma:

```text
|H|=3, every |E|>=3, tau(H)>=3  implies  |B(H)|>=27.          (2.3)
```

Indeed, the three members must be pairwise disjoint, and every choice of one
point from each is a distinct minimal transversal.

## 3. Strengthened four-member lemma

### Lemma 3.1

`PROVED`: if `H` is a finite clutter with four members, every member has size
at least three, and `tau(H)>=3`, then

```text
|B(H)| >= 9.                                                  (3.1)
```

### Proof

Form the intersection graph `J` on the four members. Two vertex-disjoint
edges of `J` would provide two points meeting all four members. Hence the
matching number of `J` is at most one.

If `J` has at least two isolated vertices, their corresponding members are
disjoint components of `H`. Blocker factorization over disjoint active ground
sets gives at least `3*3=9` minimal transversals.

Suppose `J` has exactly one isolated member `E`, and let `K` be the other
three members. Then

```text
tau(H)=tau(K)+1,
```

so `tau(K)>=2`. We claim `|B(K)|>=3`. If `|B(K)|<=2`, blocker involution and
(2.1), applied to each member of `K=B(B(K))`, would force every member of
`K` to have size at most two. This contradicts the row-size hypothesis.
Factorization now gives

```text
|B(H)|=|B(K)| |E| >= 3*3=9.
```

If `J` has no isolated vertex, the matching-number condition forces `J` to
be a three-leaf star. Fix a point in the intersection of the center and one
leaf. Choose one point independently from each of the other two leaves. The
leaves are pairwise disjoint, so this produces at least `3*3=9` distinct
three-point transversals. Every one is minimal because `tau(H)>=3`.

These cases exhaust `J`, proving (3.1). `\square`

## 4. Five-member lemma

### Lemma 4.1

`PROVED`: if `H={E_1,...,E_5}` is a finite clutter, every member has size at
least three, and `tau(H)>=3`, then

```text
|B(H)| >= 6.                                                  (4.1)
```

### Proof: high-incidence point

Ignore ground points outside the union of `H`; no minimal transversal uses
them. A point cannot belong to four or five members. Such a point, together
with at most one point from the remaining member, would give a transversal of
size at most two.

Suppose a point `x` belongs to exactly three members. The other two members
must be disjoint; an intersection point between them, together with `x`,
would again give a two-point transversal. Choosing one point from each of the
two disjoint members gives at least `3*3=9` distinct three-point
transversals with `x`. They are all minimal because `tau(H)>=3`.

It remains to assume that every active point belongs to at most two members.

### Proof: multigraph model

Represent each actual ground point by its support on the five row indices. A
point of incidence degree one is an actual loop; a point of incidence degree
two is an actual nonloop edge. Equal supports remain distinct parallel actual
points. A transversal of `H` is exactly an edge cover of these five support
vertices. Each support vertex has actual incidence degree

```text
d(i)=|E_i| >= 3.                                              (4.2)
```

Let `J` be the simple support graph of the nonloop points and let `nu` be its
matching number. Since `J` has five vertices, `nu` is `0`, `1`, or `2`.

If `nu=0`, all actual points are loops. Choosing one of at least three loops
at every vertex gives at least `3^5` minimal edge covers.

Suppose `nu=1`. The nonloop support graph is a star or a triangle together
with isolated vertices.

- In the star case, fix one actual center--leaf edge. The other three
  vertices are pairwise nonadjacent. Choose one of their at least three
  incident actual points independently. Each selected point has its
  corresponding vertex as a private witness, while the fixed edge has its
  leaf as a private witness. This gives at least `3^3=27` minimal covers.
- In the triangle case, fix two adjacent actual triangle edges. The other two
  vertices are isolated and each has at least three actual loops. The fixed
  edges cover the triangle minimally, and independent loop choices give at
  least `3^2=9` minimal covers.

It remains that `nu=2`. Fix an actual two-edge matching

```text
M={e_1,e_2}
```

and let `w` be its unmatched support vertex. For every actual point `p`
incident with `w`, the set

```text
M union {p}                                                    (4.3)
```

is a three-point edge cover. It is minimal because two points, each with
support size at most two, cannot cover five vertices. Thus (4.3) gives a
family `F_M` of `d(w)>=3` distinct blockers.

Assume first that there is another actual two-edge matching `N`. If `M` and
`N` share no actual point, `F_M` and `F_N` are disjoint: a three-point set
cannot contain four distinct matching points. Hence their union has at least
six members.

Suppose instead that

```text
M={e,f}, N={e,g}.
```

If `f` and `g` are distinct parallel actual points, the two generated
families are again disjoint, since `{e,f,g}` misses their common unmatched
vertex. Otherwise their two supports are distinct two-subsets of the three
vertices outside the support of `e`; their union covers those three vertices.
The families `F_M` and `F_N` then intersect in at most `{e,f,g}`, so their
union has at least five members.

Write the support of `e` as `{u,v}`. By (4.2), choose actual points
`r_u!=e` incident with `u` and `r_v!=e` incident with `v`. The set

```text
{r_u,r_v,f,g}
```

covers all five support vertices. Any inclusion-minimal subcover of it avoids
`e`, whereas every member of `F_M union F_N` contains `e`. It supplies a
sixth blocker.

Finally suppose `M` is the unique actual two-edge matching. Every point
incident with `w` must be a loop at `w`; a nonloop from `w` to an endpoint of
one matching edge would be disjoint from the other matching edge. Hence `w`
has at least three distinct actual loops.

Write the support of `e_1` as `{u,v}`. Choose `r_u!=e_1` incident with `u`
and `r_v!=e_1` incident with `v`. The set `{r_u,r_v,e_2}` covers the four
vertices matched by `M`. Take an inclusion-minimal subcover `K` of those four
vertices. For each loop `l` at `w`,

```text
K union {l}
```

is a minimal cover of all five vertices. These at least three covers avoid
`e_1`: minimality of `K` supplies a private matched vertex for every point of
`K`, and the loop `l` has `w` as a private vertex. The at least three members
of `F_M` contain `e_1`. Thus there are at least six blockers.

All cases prove (4.1). `\square`

## 5. Local and global deductions

Assume a mutual-blocker pair from (1.1) has `a+b<=10`. Exchange the two sides
if needed so that `a<=b`. By (2.2), `a` is `3`, `4`, or `5`.

- If `a=3`, (2.3) gives `b>=27`.
- If `a=4`, Lemma 3.1 gives `b>=9`.
- If `a=5`, Lemma 4.1 gives `b>=6`.

Every case contradicts `a+b<=10`. This proves (1.1).

The accepted G4.5 middle-layer interface is an admissible pair of this type,
so `|A_3|>=11`. Combining it with the frozen other-layer bounds proves the
candidate consequence (1.2) on every finite trace ground set and hence in the
frozen eventual-stability reduction.

## 6. Computation and remaining boundary

`COMPUTED`: the companion incidence-pattern search exhaustively found no
total-ten `(5,5)` pair and no total-eleven `(5,6)` pair. The total-ten result
is regression evidence for the theorem above. The total-eleven zero hit is
not used to claim `m(3,3)>=12`.

The deterministic search visited `6938170` DFS nodes for `(5,5)` and
`30357960` nodes for `(5,6)`. It uses exact integer multiplicities for every
nonzero incidence pattern, the private-witness member-size cap, and row-
permutation canonicalization. Its semantic blocker implementations agree on
all `199` clutters on ground sizes at most four. The replay command is

```text
UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run python \
  Problems/P0054/experiments/g4.6-middle-ten/search.py
```

The search source SHA-256 is
`c502ef271b9d028feb5fabdbf1f162cb760cf98c3870c8a8d710f318e46e6124`.
The saved output SHA-256 is
`8ea53c6fcdf415ab2f6ec662bbe42569aec15cd47d51698d0cbb7e3ff1b1ce3c`.

`UNKNOWN`: exact `m(3,3)`, exact `sat(7)`, compatibility of a hypothetical
eleven-member middle layer with the equality cases in `A_2` and `A_4`,
novelty, and priority.

No claim or status file is modified by this candidate.
