# P0054 G4.3 dependency-resolved candidate proof

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_3_EIGHT_MEMBER_LAYER_EXCLUSION
CANDIDATE_THEOREM: sat(7) >= 41
CANDIDATE_STATUS: DEPENDENCY_RESOLVED_PENDING_TWO_REFEREES
NETWORK: OFFLINE; NOT_USED
FORMALIZER: FORBIDDEN; NOT_USED
COMMIT_PUSH_PUBLICATION: FORBIDDEN; NOT_USED
```

## 1. Exact statement and evidence boundary

`PROVED` relative to the frozen G4.2 global interface and the deductions below:
for every finite set `U`, if two clutters `mathcal S,mathcal C` satisfy

```text
mathcal S = B(mathcal C),
mathcal C = B(mathcal S),
|S| >= 2 for every S in mathcal S,
|C| >= 4 for every C in mathcal C,
```

then

```text
|mathcal S| + |mathcal C| >= 9.                            (1)
```

Thus the local parameter in the frozen statement satisfies `m(2,4)>=9`.
The proof does not bound `|U|`.

`PROVED` relative to the same frozen framework: the second and fourth
canonical layers satisfy `|A_2|>=9` and `|A_4|>=9`. Together with the other
accepted layer bounds, this gives the candidate global theorem

```text
sat(7) >= 41.                                               (2)
```

`DEFINITION`: `PROVED` in this candidate records a dependency-resolved
deduction awaiting the two required isolated Referees. P0054-C19 may be
created only after both Referees return `ACCEPT`.

`DEFINITION`: every finite search result remains `COMPUTED`. No solver,
incidence-pattern search, or finite-core certificate is a dependency of this
proof.

## 2. Frozen global and local interfaces

`PROVED` (frozen P0054-C17/P0054-C18 framework): on a sufficiently large
ground set in the eventual stable range, choose an endpoint-normal minimum
saturated 7-Sperner family `F`. The established upper bound `sat(7)<=55`
forces a homogeneous all-or-none block `H`. Its canonical decomposition has
seven nonempty saturated-antichain layers

```text
F = A_0 disjoint-union ... disjoint-union A_6
```

with accepted bounds

```text
(|A_0|,...,|A_6|) >= (1,6,8,9,8,6,1).                     (3)
```

Put `U=X\H`. For `A_2`, let `mathcal S` be its small members and let
`mathcal C` be the complements in `U` of its large traces. The frozen G4.2
blocker recognition proves

```text
mathcal S = B(mathcal C),    mathcal C = B(mathcal S),      (4)
|S| >= 2,                    |C| >= 4.                       (5)
```

The member count of `A_2` is exactly
`|mathcal S|+|mathcal C|`, because complementing large traces is a bijection.
All of (4)--(5) quantify an arbitrary finite `U`; they are not a fixed-core
enumeration.

`PROVED` (frozen complemented interface): for `A_4`, its original small
members have size at least four and the complements of its large traces have
size at least two. Swapping those two complemented sides produces a pair of
the form (4)--(5), with the same total member count.

## 3. Blocker definitions and empty-side boundary

`DEFINITION`: a transversal of a family `mathcal H` is a subset of `U`
meeting every member of `mathcal H`. Its blocker `B(mathcal H)` is the family
of inclusion-minimal transversals. A clutter is an ordinary set-family
antichain, not a multiset. We use `B(empty family)={empty set}`.

`PROVED`: both sides of an admissible pair are nonempty. If `mathcal C` were
empty, then `mathcal S=B(mathcal C)={empty set}`, contradicting the lower
bound two. If `mathcal S` were empty, then
`mathcal C=B(mathcal S)={empty set}`, contradicting the lower bound four.

`PROVED`: every transversal of a finite family contains an inclusion-minimal
transversal. Starting with the transversal, repeatedly delete a point while
the transversal property remains; finiteness terminates. This fact is used
below without any choice or compactness argument.

## 4. Private-witness lemma

`PROVED` (**private-witness lemma**): if `T in B(mathcal H)`, then for every
`x in T` there is a member `E_x in mathcal H` such that

```text
T intersect E_x = {x}.                                     (6)
```

Indeed, minimality says `T\{x}` is not a transversal. Hence some
`E_x in mathcal H` is disjoint from `T\{x}`. Since `T` is a transversal,
`x in E_x`, proving (6).

`PROVED`: distinct points have distinct private witnesses. If `x!=y` but
`E_x=E_y`, then the same intersection with `T` would equal both `{x}` and
`{y}`, which is impossible. Thus `x -> E_x` is an injection and

```text
|T| <= |mathcal H|.                                        (7)
```

The empty blocker member creates no exception: when `T=empty`, (7) is
vacuous.

Put

```text
a=|mathcal S|,    b=|mathcal C|.
```

`PROVED`: choose any `C in mathcal C=B(mathcal S)`. Equations (5) and (7)
give `4<=|C|<=a`, so `a>=4`. Similarly, any
`S in mathcal S=B(mathcal C)` gives `2<=|S|<=b`, so `b>=2`.

Therefore, under the requested contradiction hypothesis `a+b=8`, the only
possible splits are

```text
(a,b)=(4,4), (5,3), (6,2).                                (8)
```

No conclusion about these splits has yet been assumed.

## 5. Exclusion of `(a,b)=(6,2)`

Write `mathcal C={C_1,C_2}`.

`PROVED`: `C_1` and `C_2` are disjoint. If
`x in C_1 intersect C_2`, then `{x}` is a transversal of `mathcal C`.
It is inclusion-minimal because both `C_i` are nonempty. Hence
`{x} in B(mathcal C)=mathcal S`, contradicting `|S|>=2`.

`PROVED`: for every `x in C_1` and `y in C_2`, the pair `{x,y}` is an
inclusion-minimal transversal of `mathcal C`. It meets both sets, while
deleting either point leaves one of the two disjoint sets unhit. Disjointness
also makes different ordered choices `(x,y)` produce different two-element
sets. Therefore

```text
a=|B(mathcal C)| >= |C_1||C_2| >= 4*4 = 16,                (9)
```

contradicting `a=6`. Thus the `(6,2)` split is impossible.

## 6. Three-set blocker theorem

`PROVED` (**three-set blocker theorem**): let
`mathcal C={C_1,C_2,C_3}` be three subsets of a finite `U`, each of size at
least four. If `B(mathcal C)` has no singleton member, then

```text
|B(mathcal C)| >= 12.                                      (10)
```

This theorem allows nonuniform sizes and arbitrarily repeated point-incidence
patterns. Its proof follows.

`PROVED`: the triple intersection is empty. A point in
`C_1 intersect C_2 intersect C_3` would itself be a singleton minimal
transversal.

For `{i,j,k}={1,2,3}`, define the six possible nonempty incidence classes

```text
A_i = C_i \ (C_j union C_k),
P_i = (C_j intersect C_k) \ C_i,
alpha_i = |A_i|,    pi_i = |P_i|.
```

Points outside `C_1 union C_2 union C_3` cannot occur in a minimal
transversal. The empty triple intersection means these six classes contain
every relevant point. For every `i`,

```text
|C_i| = alpha_i + pi_j + pi_k >= 4.                        (11)
```

`PROVED`: every minimal transversal has size at most three. Given a minimal
transversal `T`, choose one point of `T intersect C_i` for each `i`. The at
most three selected points form a transversal contained in `T`; minimality
forces equality.

`PROVED`: the two-element minimal transversals are exactly:

1. one point from `A_i` and one from `P_i`, for some `i`; or
2. one point from each of `P_i,P_j`, for two distinct indices.

The incidence supports in either listed pair cover all three labels and
neither support alone does. Conversely, among the six allowed singleton- or
double-label supports, these are exactly the unordered pairs whose union is
all three labels.

`PROVED`: the three-element minimal transversals are exactly the sets with
one point in each of `A_1,A_2,A_3`. For the forward direction, apply the
private-witness lemma to a three-element minimal transversal. Its three
private witnesses are distinct members of the three-set family, so the
witness labels form a bijection. A point cannot lie in either of the other
two witness sets, because it would destroy the corresponding singleton
intersection. Thus each point has a singleton incidence support, one for
each label. The converse is immediate: deleting the `A_i` point leaves
`C_i` unhit.

`PROVED`: the preceding disjoint classification gives the exact count

```text
B := |B(mathcal C)|
   = alpha_1 alpha_2 alpha_3
     + sum_i alpha_i pi_i
     + pi_1 pi_2 + pi_1 pi_3 + pi_2 pi_3.                  (12)
```

`PROVED`: if some `pi_i>=3`, the terms of (12) containing `pi_i` give

```text
B >= pi_i(alpha_i+pi_j+pi_k)
  =  pi_i |C_i| >= 3*4 = 12.                              (13)
```

It remains to consider `0<=pi_i<=2` for all `i`. Equation (11) gives

```text
alpha_i >= alpha_i^(0) := 4-pi_j-pi_k >= 0.                (14)
```

The right side of (12) is nondecreasing in each `alpha_i`: increasing
`alpha_i` by one changes it by `alpha_j alpha_k+pi_i>=0`. By symmetry order
`pi_1<=pi_2<=pi_3`; the following ten rows exhaust the multisets from
`{0,1,2}`. Substitution of the lower values (14) gives:

| `(pi_1,pi_2,pi_3)` | `(alpha_1^(0),alpha_2^(0),alpha_3^(0))` | `B_0` |
|---|---:|---:|
| `(0,0,0)` | `(4,4,4)` | 64 |
| `(0,0,1)` | `(3,3,4)` | 40 |
| `(0,0,2)` | `(2,2,4)` | 24 |
| `(0,1,1)` | `(2,3,3)` | 25 |
| `(0,1,2)` | `(1,2,3)` | 16 |
| `(0,2,2)` | `(0,2,2)` | 12 |
| `(1,1,1)` | `(2,2,2)` | 17 |
| `(1,1,2)` | `(1,1,2)` | 13 |
| `(1,2,2)` | `(0,1,1)` | 12 |
| `(2,2,2)` | `(0,0,0)` | 12 |

Thus (10) holds in every case. This finite ten-row arithmetic audit classifies
three bounded incidence multiplicities after the unbounded case (13); it is
not an enumeration of `U` or a finite-ground extrapolation.

## 7. Exclusion of `(a,b)=(5,3)`

`PROVED`: because `mathcal S=B(mathcal C)` and every member of `mathcal S`
has size at least two, `B(mathcal C)` has no singleton. The three-set blocker
theorem gives

```text
a=|B(mathcal C)|>=12,
```

contradicting `a=5`. Thus the `(5,3)` split is impossible. The theorem has
been proved inside this candidate rather than imported as an unabsorbed
Prover report.

## 8. Exclusion of `(a,b)=(4,4)`

`PROVED`: every `C in mathcal C=B(mathcal S)` has size exactly four. The
assumption gives `|C|>=4`, while the private-witness bound gives
`|C|<=|mathcal S|=4`.

`PROVED`: every transversal of `mathcal S` has size at least four. It
contains a minimal transversal; that member of
`B(mathcal S)=mathcal C` has size exactly four.

`PROVED`: the four members of `mathcal S` are pairwise disjoint. If two met
at a point `x`, choose one point from each of the other two nonempty members.
Those at most three points would meet all four members, contradicting the
preceding transversal lower bound.

`PROVED`: choose one point from each of the four pairwise-disjoint members of
`mathcal S`. The resulting four-point set is an inclusion-minimal
transversal: deleting the point chosen from `S_i` leaves `S_i` unhit.
Different choices give different subsets, because intersection with each
disjoint `S_i` recovers its chosen point. Hence

```text
|B(mathcal S)| >= product_(S in mathcal S) |S| >= 2^4=16,   (15)
```

contradicting `|B(mathcal S)|=|mathcal C|=4`. Thus the `(4,4)` split is
impossible.

## 9. The arbitrary-finite-`U` local theorem

`PROVED`: no admissible pair has total size at most eight. The requested
equality-eight case is exhausted by (8) and Sections 5, 7, and 8. For
completeness, the smaller-total boundary follows from the same arguments:
after `a>=4,b>=2`, if `b=2` then (9) gives `a>=16`; if `b=3` then (10) gives
`a>=12`; and if `b>=4`, total at most eight forces exactly `(a,b)=(4,4)`,
already excluded. Therefore (1) holds without relying on a finite search or
on the older numerical bound `m(2,4)>=8`.

`UNKNOWN`: this proof does not determine whether equality nine occurs and
does not determine the exact value of `m(2,4)`. Any later bounded search for
that stronger question is separate from the proof of (1).

## 10. Application to `A_2` and `A_4`

`PROVED`: apply Section 9 to the frozen pair (4)--(5). Since its total is the
actual layer size,

```text
|A_2| >= 9.                                                (16)
```

`PROVED`: for `A_4`, let `mathcal S_4` be the original small family and
`mathcal C_4` the complements of its large traces. The frozen interface has

```text
mathcal S_4=B(mathcal C_4),    mathcal C_4=B(mathcal S_4),
|S_4|>=4,                      |C_4|>=2.
```

Define the second-layer-oriented pair

```text
mathcal S' = mathcal C_4,    mathcal C' = mathcal S_4.
```

Then `mathcal S'=B(mathcal C')`, `mathcal C'=B(mathcal S')`, its member-size
lower bounds are two and four, and its total cardinality is `|A_4|`. Section
9 gives

```text
|A_4| >= 9.                                                (17)
```

This is a side swap of an arbitrary finite-set interface, not an assumption
that the original global family is complement-symmetric.

## 11. Global sum and eventual quantifier

`PROVED`: insert (16)--(17) into the accepted frozen global layer framework:

```text
|F| >= 1+6+9+9+9+6+1 = 41.                                (18)
```

The frozen construction chose the ground set in the eventual stable range
and chose `F` minimum there. Hence

```text
sat(7)=sat(n,7)=|F|>=41.
```

This is a global eventual lower bound, not a fixed-core or common-block
template-class claim. The homogeneous block was forced upstream for a global
minimum family by the already proved upper bound 55.

## 12. Boundary and quantifier audit

- `PROVED`: `U` is arbitrary and finite; no upper bound on `|U|` appears.
- `PROVED`: both empty sides are explicitly excluded, and all chosen member
  points exist because the lower size bounds are positive.
- `PROVED`: nonuniform member sizes are allowed. Every count uses only the
  stated lower bounds; larger sizes can only increase the product bounds or
  the incidence-class lower constraints.
- `PROVED`: repeated point-incidence patterns are allowed. The variables
  `alpha_i,pi_i` are arbitrary multiplicities, including zero and unbounded
  values; actual distinct points, not quotient patterns, are counted.
- `PROVED`: the families are ordinary clutters. No duplicate set is counted
  twice, and complementing or swapping sides preserves antichains.
- `PROVED`: blocker minimality is used explicitly in the private-witness
  lemma, the size-at-most-three classification, and every product count.
- `PROVED`: points outside the union of a family never occur in one of its
  minimal transversals, so unused coordinates in arbitrarily large `U` do not
  create a missing case.
- `PROVED`: no probability, floating-point comparison, division, limit,
  compactness, finite-`q` extrapolation, solver certificate, or Formalizer is
  used.
- `PROVED`: the `A_4` argument swaps an already recognized mutual-blocker
  pair and preserves every quantifier and the total member count.
- `PROVED`: C1--C18 remain frozen. Nothing here asserts an exact value,
  novelty, priority, a formalization status, a solved status, or publication
  readiness.

## 13. Dependency ledger

| Node | Status | Depends on |
|---|---|---|
| frozen global canonical framework | `PROVED` | accepted P0054-C17/P0054-C18 framework and P0054-C7 |
| mutual-blocker local interface | `PROVED` | frozen G4.2 oriented cover and antichains |
| private-witness lemma | `PROVED` | blocker minimality |
| `(6,2)` exclusion | `PROVED` | singleton exclusion and disjoint-product count |
| three-set blocker lower bound 12 | `PROVED` | six incidence classes and exact integer count |
| `(5,3)` exclusion | `PROVED` | three-set blocker theorem |
| `(4,4)` exclusion | `PROVED` | transversal number and disjoint-product count |
| `m(2,4)>=9` | `PROVED` | exhaustive split and smaller-total audit |
| `|A_2|,|A_4|>=9` | `PROVED` | local theorem and frozen dual interface |
| `sat(7)>=41` | `PROVED` | frozen remaining layer bounds and eventual quantifier |

```text
FIRST_UNCERTAIN_MATHEMATICAL_STEP: NONE_WITHIN_FROZEN_DEPENDENCIES
UNRESOLVED_MATHEMATICAL_DEPENDENCIES: NONE
SIZE8_COUNTEREXAMPLE: NONE
FINITE_COMPUTATION_USED_AS_PROOF: NO
REFEREE_STATUS: NOT_YET_RUN
CLAIMS_OR_STATUS_MODIFIED: NO
```
