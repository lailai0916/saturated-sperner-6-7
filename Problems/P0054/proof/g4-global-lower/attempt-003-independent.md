# Attempt 003 — independent global reconstruction

## Isolation, scope, and verdict

- `DEFINITION`: this is the isolated offline Prover C route for
  `P0054_G4_GLOBAL_LOWER_BOUND_FOR_sat7`.
- `DEFINITION`: the only research target in this attempt is the candidate
  global inequality `sat(7) >= 37`. No stronger bound is investigated.
- `DEFINITION`: this attempt used the frozen G4 literature pack, the verified
  Martin--Veldt VOR snapshot with SHA-256
  `e5183031a356080e053ead0766373b4f62eed130e3020b72003617030d670cf2`,
  and the Section 0 materials. It did not read attempts 001 or 002 or the G4
  experimental report, and it used no network access.
- `PROVED`: accepting the frozen `LITERATURE` inputs listed below, the proof
  in this document establishes `sat(7) >= 37` with the eventual-stability
  quantifier made explicit.
- `DEFINITION`: the preceding line is a Prover-route result, not authorization
  to add a repository claim. Main-Agent synthesis and the required Referees
  remain outside this attempt.

## Exact theorem

**Theorem.** `PROVED`: let `sat(7)` denote the eventual stable value of the
minimum cardinality of a saturated 7-Sperner family on an `n`-element ground
set. Then

```text
sat(7) >= 37.
```

Here a 7-Sperner family contains no chain of eight distinct sets, and
saturation means that adjoining any omitted set creates such an eight-set
chain.

## Frozen dependencies

The proof uses the following dependencies and no class-restricted G0--G3
lower-bound certificate.

1. `LITERATURE` (Gerbner--Keszegh--Lemons--Palmer--Pálvölgyi--Patkós,
   2013): for fixed `k`, `sat(n,k)` is eventually stable; for `2 <= k <= n`,
   one may choose a minimum-cardinality saturated `k`-Sperner family that
   contains both the empty set and the complete ground set.
2. `PROVED` (existing P0054-C7): `sat(7) <= 55`.
3. `LITERATURE` (Martin--Veldt, 2025, Lemma 6): if a finite family `F` on
   `X` satisfies `|X| > 2^|F|`, it has a homogeneous atom `H` with
   `|H| >= 2`. Every member of `F` either contains all of `H` or is disjoint
   from `H`.
4. `LITERATURE` (Martin--Veldt, 2025, Definitions 9--10 and Lemma 13): the
   canonical decomposition of a saturated `k`-Sperner family having a
   homogeneous atom consists of saturated antichains.
5. `LITERATURE` (Martin--Veldt, 2025, Lemma 15): for a minimum-cardinality
   saturated `k`-Sperner family in this homogeneous canonical setup, the first
   internal layer contains at least `k-2` small singletons and one large
   member; the dual assertion holds for the last internal layer.

The proof below independently derives the exact number of nonempty canonical
layers, the endpoint layers, the small/large size restrictions, and all three
internal probabilistic bounds. Thus the statement of Martin--Veldt
Proposition 14 is not used as an unexpanded bridge.

## Proof

### 1. Stable ground-set choice and homogeneous atom

Let `s = sat(7)`. By eventual stability there is an integer `N` such that
`sat(n,7)=s` for every `n >= N`. Choose an integer

```text
n >= N,    n >= 7,    and    n > 2^55,
```

and let `X` be an `n`-element set. By the endpoint-normalization result in
Dependency 1, choose a minimum-cardinality saturated 7-Sperner family
`F subseteq P(X)` such that

```text
empty in F,    X in F,    and    |F| = sat(n,7) = s.
```

Dependency 2 gives `|F|=s<=55`; hence

```text
|X| = n > 2^55 >= 2^|F|.
```

Dependency 3 therefore supplies a homogeneous atom `H` of `F` with
`|H|>=2`. This is the actual VOR threshold; no assumption `|H|>2` is used.
Write

```text
U = X \ H.
```

The use of `sat(7)<=55` ends here. It is used only to select a stable ground
set large enough for the atom theorem, so there is no circular use of the
candidate lower bound.

### 2. Exactly seven nonempty canonical layers

`PROVED`: `F` is a proper subfamily of `P(X)`, since
`|F|<=55<2^n`. Choose `T in P(X)\F`. Saturation says that `F union {T}`
contains an eight-set chain. Exactly seven members of that chain lie in `F`,
so `F` contains a seven-set chain. The 7-Sperner condition forbids an
eight-set chain in `F`. Consequently the height of `F`, as an inclusion
poset, is exactly seven.

For `A in F`, let `ell(A)` be the largest number of strict inclusions in a
chain in `F` ending at `A`. In a finite poset, iterative removal of minimal
elements places `A` in canonical layer

```text
A_i  if and only if  ell(A)=i.
```

For completeness, this follows by induction on `i`: elements with
`ell=0` are precisely the minimal elements; after all levels below `i` have
been removed, an element with level `i` has no remaining predecessor, while
an element of larger level has a predecessor on a longest chain that remains.

It follows that the canonical decomposition is the disjoint union

```text
F = A_0 disjoint-union ... disjoint-union A_6.
```

Every layer is nonempty. Indeed, on any seven-member chain in `F`, the member
in position `i` has level exactly `i`: a longer chain ending there could be
continued by the remaining members and would produce a chain in `F` longer
than seven.

Each `A_i` is an antichain: if `B proper-subset C` were in the same layer,
appending `C` to a longest chain ending at `B` would give
`ell(C)>ell(B)`. Also, if `i>0` and `C in A_i`, a longest chain ending at `C`
contains a predecessor `B in A_(i-1)` with `B proper-subset C`. Thus the
canonical layers are layered without an extra assumption.

Dependency 4 now applies with the single atom `H` already obtained for all of
`F`, and gives:

```text
each A_i is a saturated antichain in P(X).
```

### 3. Endpoint layers and internal size restrictions

`PROVED`: because `empty in F` and the empty set is below every other member,
it is the unique minimal member. Hence

```text
A_0 = {empty}.
```

Every seven-member chain in `F` ends at `X`: if its top were a proper subset
of `X`, adjoining `X in F` would produce an eight-member chain in `F`.
Therefore `ell(X)=6`, so `X in A_6`. Since `A_6` is an antichain and every
other member of `F` is a proper subset of `X`,

```text
A_6 = {X}.
```

`PROVED`: every `B in A_i` with `i<6` has a strict successor in `A_(i+1)`.
Since `A_(i+1)` is saturated and does not contain `B`, some `C in A_(i+1)`
is strictly comparable with `B`. If `C proper-subset B`, layering supplies
`D in A_i` with

```text
D proper-subset C proper-subset B,
```

contradicting that `A_i` is an antichain. Hence `B proper-subset C`.

Call a member small when it is disjoint from `H`, and large when it contains
`H`. If a small `S in A_i` is followed down through canonical predecessors to
`A_0`, every predecessor is also small. There are `i` strict inclusions from
the empty set to `S`, whence

```text
|S| >= i.                                                   (1)
```

If a large `L in A_i` is followed up through the strict successors just
proved to `A_6={X}`, every successor is also large. There are `6-i` strict
inclusions from `L` to `X`, whence

```text
|X \ L| >= 6-i.                                             (2)
```

Dependency 5 at `k=7` gives at least five small singleton members and one
large member in `A_1`, and the dual statement in `A_5`. Therefore

```text
|A_1| >= 6    and    |A_5| >= 6.                            (3)
```

Together with the endpoint result,

```text
|A_0|=|A_6|=1.                                              (4)
```

### 4. Exact finite weighted-cover lemma

Fix `i in {2,3,4}`. Let `S_i` be the small members of `A_i`. For every large
member `L in A_i`, put `K=L\H subseteq U`, and let `K_i` be the family of
these core traces.

Choose once and for all a set `Q` satisfying

```text
empty proper-subset Q proper-subset H.
```

Such a `Q` exists because `|H|>=2`. For every `R subseteq U`, the set
`R union Q` is neither disjoint from `H` nor contains all of `H`; hence it is
not a member of `F`, including when `R` equals the core trace of a member.
Since `A_i` is a saturated antichain, `R union Q` is strictly comparable with
some member of `A_i`.

If that member is small, it cannot contain the nonempty set `Q`, so it must be
below `R union Q` and hence be a subset of `R`. If that member is large, it
cannot be below a set missing `H\Q`, so `R union Q` must be below it and hence
`R` must be a subset of its core trace. Therefore, for every `R subseteq U`,

```text
1 <= Z_i(R)
   := sum_(S in S_i) 1[S subseteq R]
      + sum_(K in K_i) 1[R subseteq K].                     (5)
```

This proves the coverage pointwise; it does not assume that either the small
or large side is nonempty.

Now include every element of `U` in `R` independently with a rational
probability `p`, where `0<p<1`. This is a finite probability space in which
every `R subseteq U` has positive probability. Taking expectation in (5)
gives the exact identity and bounds

```text
1 <= E[Z_i]
   = sum_(S in S_i) p^|S|
     + sum_(K in K_i) (1-p)^|U\K|
   <= |S_i| p^i + |K_i| (1-p)^(6-i),                       (6)
```

where the last inequality uses (1), (2), and `0<p<1`. Equation (6) is an
exact finite rational double count; no floating-point approximation is
involved.

### 5. The second and fourth internal layers

Put `a=|S_2|`, `b=|K_2|`, and `m=|A_2|=a+b`. With `p=2/5`, (6) gives

```text
1 <= (4/25)a + (81/625)b
  <= (4/25)(a+b) = (4/25)m.
```

If `m<=6`, the right side is at most `24/25<1`, a contradiction. Hence

```text
|A_2| >= 7.                                                 (7)
```

For `A_4`, put `p=3/5`. The small and large weights in (6) are respectively
`81/625` and `4/25`, so the same exact comparison gives

```text
1 <= (81/625)|S_4| + (4/25)|K_4|
  <= (4/25)|A_4|.
```

Thus

```text
|A_4| >= 7.                                                 (8)
```

The arguments for (7) and (8) remain valid if either side of the layer is
empty.

### 6. The middle layer and exclusion of equality eight

For `i=3` and `p=1/2`, both event probabilities in (6) are at most `1/8`.
Writing `m=|A_3|` gives

```text
1 <= E[Z_3] <= m/8,
```

so `m>=8`.

Assume for contradiction that `m=8`. Every inequality above is then an
equality. In particular:

1. every small member has cardinality exactly three and every large member
   has complement of cardinality exactly three, since each of the eight event
   probabilities must equal `1/8`;
2. `Z_3(R)=1` for every `R subseteq U`, since `Z_3(R)-1` is nonnegative at
   every point, every point has positive probability, and its expectation is
   zero.

Let `a` and `b` be the numbers of small and large members. At `R=empty`, no
small event occurs because every small member has size three, while every
large down-closure event occurs. Thus

```text
1 = Z_3(empty) = b.
```

At `R=U`, every small up-closure event occurs, while no large event occurs:
`U subseteq K` would force `|U\K|=0`, contrary to the forced value three.
Thus

```text
1 = Z_3(U) = a.
```

This gives `m=a+b=2`, contradicting `m=8`. Therefore

```text
|A_3| >= 9.                                                 (9)
```

There is also a direct overlap check of the same equality obstruction. The
up-closures of two distinct small members meet at their union, and the
down-closures of two distinct large core traces meet at their intersection.
Hence the identity `Z_3=1` permits at most one member of each type, again
contradicting eight total members.

### 7. Summation and the eventual quantifier

The canonical layers are pairwise disjoint and exhaust `F`. Combining
(3), (4), (7), (8), and (9) gives

```text
s = |F|
  = sum_(i=0)^6 |A_i|
  >= 1 + 6 + 7 + 9 + 7 + 6 + 1
  = 37.
```

The chosen `n` lies in the stable range, so `|F|=sat(n,7)=sat(7)`. This proves
the theorem with no statement restricted to a common-block template class.

## Equality, boundary, and counterexample audit

- `PROVED`: the homogeneous threshold used is `|H|>=2`; this is exactly what
  is needed to choose a nonempty proper `Q subset H`.
- `PROVED`: `F` is proper, so the saturation argument producing a seven-chain
  is not vacuous.
- `PROVED`: all seven canonical layers are nonempty; this is derived from
  height exactly seven, not assumed from notation.
- `PROVED`: the same atom `H` belongs to the whole family before the canonical
  decomposition is taken, so no layerwise atom-quantifier swap occurs.
- `PROVED`: the coverage test set `R union Q` never belongs to `F`, including
  when `R` is `empty`, `U`, a small member, or a large member's core trace.
- `PROVED`: the estimates for `A_2` and `A_4` allow an empty small side or an
  empty large side.
- `PROVED`: in the hypothetical middle equality case, `R=empty` and `R=U`
  force one member of each type; thus neither an empty side nor eight members
  can survive. Pairwise upper-/lower-closure intersections independently
  expose the same contradiction.
- `PROVED`: all integer rounding is exact: `24/25<1`, and the middle case is
  eliminated rather than rounded from a floating-point value.
- `PROVED`: `sat(7)<=55` is used only to make the atom theorem applicable at
  an arbitrarily chosen stable `n`; the final lower-bound summation does not
  depend on that upper bound.

No counterexample to any lemma above remains after these boundary checks.

## Source cross-check and prior-art caution

`LITERATURE`: the printed Martin--Veldt Lemma 17, when specialized to
`k=7`, numerically points to the same layer bounds: its formula gives a value
`2^(8/3)>6` at `i=2` and the value `8` at `i=3`, with a printed strict
inequality. However, in the displayed proof of that lemma, the exponential
comparison becomes equality at the central specialization (`i=3`, where its
epsilon is zero). The printed proof does not spell out the eight-member
equality exclusion.

`PROVED`: Section 6 above supplies that missing equality analysis directly
from exact pointwise coverage. This observation does not support novelty or
priority wording; at minimum, `37` is extremely close to an immediate
specialization of published statements and must be classified by the main
Agent and Referees, not by this isolated Prover.

## Dependency and failure ledger

```text
DEPENDENCIES:
  - eventual stability of sat(n,7) [LITERATURE]
  - endpoint-normalized minimum family [LITERATURE]
  - P0054-C7 sat(7)<=55 [PROVED]
  - homogeneous-atom lemma at |X|>2^|F| [LITERATURE]
  - canonical layers are saturated antichains [LITERATURE]
  - Martin--Veldt Lemma 15 endpoint-internal layer bound [LITERATURE]
  - finite exact double counting and the proofs in this document [PROVED]
FIRST_UNCERTAIN_STEP: NONE_WITHIN_THE_FROZEN_LITERATURE_DEPENDENCIES
UNRESOLVED_MATHEMATICAL_GAPS: NONE_IN_THIS_ATTEMPT
FAILED_ROUTE: NONE
STRONGER_BOUND_ATTEMPT: NOT_RUN_BY_SCOPE
CLASS_RESTRICTED: NO
NETWORK_USED: NO
FORMALIZER_USED: NO
```
