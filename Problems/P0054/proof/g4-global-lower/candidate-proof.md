# P0054 G4 dependency-resolved candidate proof

```text
RUN_MODE: GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_GLOBAL_LOWER_BOUND_FOR_sat7
CANDIDATE_THEOREM: sat(7) >= 37
CANDIDATE_STATUS: DEPENDENCY_RESOLVED_PENDING_TWO_REFEREES
CLASS_RESTRICTED: NO
NETWORK_AFTER_LITERATURE_FREEZE: FORBIDDEN; NOT_USED
FORMALIZER_USED: NO
PUBLICATION_AUTHORIZED: NO
```

## 1. Exact statement and evidence boundary

`DEFINITION`: `sat(n,7)` is the minimum cardinality of a saturated
7-Sperner family on an `n`-element ground set, and `sat(7)` is its eventual
stable value. A 7-Sperner family contains no strict chain of eight members;
it is saturated when adjoining any omitted set creates such a chain.

**Candidate theorem.** `PROVED` relative to the six frozen `LITERATURE`
dependencies listed in Section 2:

```text
sat(7) >= 37.
```

`DEFINITION`: in this file, `PROVED` records that the displayed deduction is
dependency-resolved. It does not create repository claim P0054-C17. The G4
gate may add that claim only if both required offline Referees return
`ACCEPT`.

`REFUTED`: the stronger Phase 2 wording that one fixed `H` must remain a
maximal homogeneous **atom** of every canonical layer is false. The proof
uses the correct weaker fact: one fixed `H` is an inherited all-or-none block
for every layer, while the layers are separately known to be saturated
antichains. Atom maximality inside a layer is never used.

## 2. Frozen dependencies

The candidate proof uses exactly these external or pre-G4 inputs.

1. `LITERATURE`: for fixed `k`, `sat(n,k)` is eventually constant
   (Gerbner--Keszegh--Lemons--Palmer--Pálvölgyi--Patkós, 2013).
2. `LITERATURE`: when `2 <= k <= n`, a minimum saturated `k`-Sperner family
   may be selected with both endpoints `empty` and `X` present (Gerbner et
   al., Lemma 6).
3. `PROVED`: existing claim P0054-C7 gives `sat(7) <= 55`. It is used only to
   select a sufficiently large stable ground set.
4. `LITERATURE`: if `|X| > 2^|F|`, then `F` has a homogeneous atom `H` with
   `|H| >= 2` (Martin--Veldt 2025, VOR Lemma 6). Thus each member of `F`
   either contains all of `H` or is disjoint from `H`.
5. `LITERATURE`: for a saturated `k`-Sperner family with such an atom, every
   canonical layer is a saturated antichain (Martin--Veldt Lemma 13 / MNS
   Lemma 17).
6. `LITERATURE`: in the endpoint-normal minimum-family setup,
   Martin--Veldt Lemma 15 gives at `k=7`
   `|A_1| >= 6` and `|A_5| >= 6`.

`PROVED`: no G0--G3 class-restricted lower-bound certificate is used in this
deduction. The only numerical G0--G3 input is the global upper bound in item
3, used before and independently of the candidate lower bound.

## 3. Stable ground set, minimum family, and atom

`PROVED`: by Dependency 1, choose `N_stab` such that

```text
sat(n,7) = sat(7)  for every n >= N_stab.
```

Choose an integer `n` satisfying

```text
n >= N_stab,    n >= 7,    and    n > 2^55,
```

and let `X` be an `n`-element set. By Dependency 2, select a
minimum-cardinality saturated 7-Sperner family `F` on `X` such that

```text
empty in F,    X in F,    and    |F| = sat(n,7) = sat(7).
```

`PROVED`: P0054-C7 gives `|F| <= 55`, so

```text
|X| = n > 2^55 >= 2^|F|.
```

Dependency 4 supplies a homogeneous atom `H` of `F` with `|H| >= 2`.
Put `U=X\H`. This selection is noncircular: the established upper bound 55,
not the candidate lower bound 37, supplies the atom threshold.

## 4. Exactly seven canonical layers

`DEFINITION`: set `R_0=F`. Let `A_i` be the inclusion-minimal members of
`R_i`, and put `R_(i+1)=R_i\A_i`.

`PROVED`: `F` is a proper subfamily of `2^X`, because
`|F|<=55<2^n`. Choose `T` outside `F`. Saturation makes
`F union {T}` contain an eight-member strict chain. That chain must contain
`T`, and removing `T` leaves a seven-member strict chain in `F`. Since `F`
is 7-Sperner, its height is exactly seven.

`PROVED`: in any finite poset, iterative removal of minimal elements places
an element `B` in `A_i` exactly when the longest strict chain in `F` ending at
`B` has `i` inclusions. This follows by induction: level-zero elements are
the minimal elements; after levels below `i` are removed, a level-`i`
element has no remaining predecessor, whereas a higher-level element retains
a predecessor on a longest chain.

`PROVED`: height seven therefore gives precisely seven nonempty, pairwise
disjoint layers

```text
F = A_0 disjoint-union A_1 disjoint-union ... disjoint-union A_6.
```

On a seven-member maximum chain, the member in position `i` has canonical
level `i`: a larger level could be followed by the remaining chain tail and
would produce height greater than seven. No layer nonemptiness is assumed.

`PROVED`: Dependency 5 applies to this canonical decomposition, so every
`A_i` is a saturated antichain in `2^X`.

`PROVED`: because every `A_i` is a subfamily of `F`, the same fixed `H` is an
all-or-none block in every layer:

```text
for every i and every B in A_i,
either H subseteq B or B cap H = empty.
```

This is the only layerwise property of `H` used below.

## 5. Endpoints, predecessors, successors, and size restrictions

`PROVED`: because `empty` belongs to `F` and is below every other member,

```text
A_0 = {empty}.
```

Every seven-member chain in `F` must end at `X`; otherwise appending
`X in F` creates an eight-member chain. Hence `X in A_6`. Since `A_6` is an
antichain and every other member is below `X`,

```text
A_6 = {X}.
```

`PROVED`: every member of `A_i`, `i>0`, has a strict predecessor in
`A_(i-1)`, by taking the preceding member of a longest chain ending there.

`PROVED`: every `B in A_i`, `i<6`, has a strict successor in `A_(i+1)`.
Since `A_(i+1)` is saturated and `B` is not in it, some `C in A_(i+1)` is
strictly comparable with `B`. If `C proper-subset B`, then a canonical
predecessor `D in A_i` of `C` would satisfy
`D proper-subset C proper-subset B`, contradicting that `A_i` is an
antichain. Therefore `B proper-subset C`.

Call a member **small** if it is disjoint from `H`, and **large** if it
contains `H`.

`PROVED`: if a small `S` belongs to `A_i`, following predecessors down to
`A_0={empty}` gives `i` strict inclusions and every predecessor is small.
Consequently

```text
|S| >= i.                                                   (1)
```

`PROVED`: if a large `L` belongs to `A_i`, following successors up to
`A_6={X}` gives `6-i` strict inclusions and every successor is large.
Consequently

```text
|X\L| >= 6-i.                                               (2)
```

`LITERATURE`: Dependency 6 gives

```text
|A_1| >= 6,    |A_5| >= 6.                                 (3)
```

Together with the endpoint calculation,

```text
|A_0| = |A_6| = 1.                                         (4)
```

## 6. Exact oriented covering lemma

Fix `i` in `{2,3,4}`. Let `S_i` be the small members of `A_i`. For each
large `L in A_i`, let `K=L\H`, a subset of `U`; let `K_i` be the collection
of these traces.

`PROVED`: since `|H|>=2`, select a nonempty proper subset `Q` of `H`. For
every `R subseteq U`, the test set

```text
T_R = R union Q
```

meets but does not contain `H`. Thus `T_R` is not in `F`, and in particular
is not in `A_i`. Saturation of the antichain `A_i` supplies a member strictly
comparable with `T_R`.

- If the member is small, it cannot contain `T_R`, because `T_R` meets `H`.
  It must therefore be contained in `T_R`, and hence in `R`.
- If the member is large, it cannot be contained in `T_R`, because `T_R`
  omits `H\Q`. It must therefore contain `T_R`, so its core trace contains
  `R`.

Hence the integer-valued covering multiplicity

```text
Z_i(R)
  = sum_(S in S_i) 1[S subseteq R]
    + sum_(K in K_i) 1[R subseteq K]
```

satisfies

```text
Z_i(R) >= 1  for every R subseteq U.                         (5)
```

`PROVED`: include each element of `U` independently in `R` with rational
probability `p`, where `0<p<1`. Taking expectations in (5) gives the exact
finite identity

```text
1 <= E[Z_i]
  = sum_(S in S_i) p^|S|
    + sum_(K in K_i) (1-p)^|U\K|.                           (6)
```

For a large member `L=K union H`, `|U\K|=|X\L|`; thus (1)--(2) apply to
both exponents. No disjointness of covering events and no floating-point
rounding is assumed.

## 7. Exact bounds for `A_2` and `A_4`

`PROVED`: for `i=2`, take `p=2/5`. Every small-event probability is at most
`(2/5)^2=4/25`; every large-event probability is at most
`(3/5)^4=81/625<4/25`. Therefore

```text
1 <= E[Z_2] <= (4/25)|A_2|.
```

If `|A_2|<=6`, the right side is at most `24/25<1`, a contradiction. Hence

```text
|A_2| >= 7.                                                  (7)
```

`PROVED`: for `i=4`, take `p=3/5`. The small and large caps are respectively
`(3/5)^4=81/625` and `(2/5)^2=4/25`. The same exact calculation gives

```text
1 <= E[Z_4] <= (4/25)|A_4|,
```

and therefore

```text
|A_4| >= 7.                                                  (8)
```

These arguments allow either side of a layer to be empty.

## 8. The middle layer and exclusion of equality eight

`PROVED`: for `i=3`, take `p=1/2`. Equations (1), (2), and (6) give

```text
1 <= E[Z_3] <= |A_3|/8,
```

so `|A_3|>=8`.

Assume for contradiction that `|A_3|=8`. Equality must hold throughout.

`PROVED`: each of the eight event probabilities is at most `1/8`, and their
sum is exactly one. Therefore every small member has size exactly three and
every large member has complement size exactly three.

`PROVED`: (5) is pointwise and the `p=1/2` distribution gives positive
probability to every `R subseteq U`. Since `E[Z_3]=1`, it follows that

```text
Z_3(R)=1  for every R subseteq U.                            (9)
```

Let `a` and `b` be the numbers of small and large members. At `R=empty`, no
small event occurs because every small member has size three, while every
large down-event occurs. Thus (9) gives `b=1`. At `R=U`, every small event
occurs, while no large event occurs because every large core trace omits
exactly three elements of `U`. Thus (9) gives `a=1`. This contradicts
`a+b=8`.

Consequently

```text
|A_3| >= 9.                                                  (10)
```

`PROVED`: the requested same-side intersection check gives the same
obstruction. Two small up-closures meet at the union of their generators;
two large down-closures meet at the intersection of their core traces.
Thus the one-fold cover (9) permits at most one member of each type.

## 9. Boundary audit

- `PROVED`: `|H|=2` is sufficient: it still has a nonempty proper subset
  `Q`. No step assumes `|H|>2`.
- `PROVED`: the test set `T_R` is outside `F` for `R=empty`, `R=U`, member
  traces, and every other `R`.
- `PROVED`: empty/full `R` are included in the pointwise cover and are used
  explicitly in the equality contradiction.
- `PROVED`: a small-empty or large-empty side causes no problem in (5)--(8).
  Under middle equality, (9) itself forces both sides to contain exactly one
  member, which contradicts eight total members.
- `PROVED`: the empty member and full member occur only in endpoint layers;
  (1)--(2) exclude them from `A_2,A_3,A_4`.
- `PROVED`: strict comparability is used only for the external test set;
  projected events correctly use non-strict containment and include
  member-self cases.
- `PROVED`: all numerical comparisons are equalities or inequalities in
  rational arithmetic. The only integer steps are `|A_2|>6`,
  `|A_4|>6`, and exclusion of `|A_3|=8`.

## 10. Summation and stable-value quantifier

`PROVED`: the seven canonical layers are disjoint and exhaust `F`. Equations
(3), (4), (7), (8), and (10) give

```text
|F|
  = sum_(i=0)^6 |A_i|
  >= 1 + 6 + 7 + 9 + 7 + 6 + 1
  = 37.
```

The selected `n` is in the stable range and `F` is a minimum family on that
ground set, so

```text
sat(7) = sat(n,7) = |F| >= 37.
```

This is a global statement about the eventual minimum, not a
`CLASS_RESTRICTED` statement.

## 11. Dependency resolution ledger

| Node | Status | Depends on |
|---|---|---|
| stable endpoint-normal minimum family | `PROVED` from `LITERATURE` | Dependencies 1--3 |
| homogeneous atom with `|H|>=2` | `PROVED` from `LITERATURE` | Dependency 4 and `n>2^55` |
| exactly seven nonempty canonical layers | `PROVED` | saturation and 7-Sperner height |
| every layer saturated antichain | `PROVED` from `LITERATURE` | Dependency 5 |
| one inherited all-or-none block | `PROVED` | `A_i subseteq F` |
| endpoint layers `1,1` | `PROVED` | endpoint normalization and height |
| first/last internal bounds `6,6` | `PROVED` from `LITERATURE` | Dependency 6 |
| internal size restrictions | `PROVED` | canonical predecessors/successors |
| oriented cover | `PROVED` | layer saturation and partial `Q subset H` |
| `A_2,A_4` bounds `7,7` | `PROVED` | exact rational cover |
| `A_3` bound `9` | `PROVED` | exact cover and equality exclusion |
| global sum `37` | `PROVED` | all preceding nodes |

`PROVED`: the dependency graph has no unresolved mathematical node inside
the frozen source boundary. Gate acceptance remains pending the two required
Referee audits.

## 12. Prior-art boundary discovered during offline proof audit

`LITERATURE`: a post-freeze implication audit of the already frozen
Martin--Veldt VOR found that the *printed statement* of Lemma 17, specialized
at `k=7`, numerically implies the same `A_2>=7` and `A_3>=9` bounds; duality
then gives `A_4>=7`. Together with Lemma 15, this is very close to a direct
published route to 37.

`PROVED`: in the printed proof of Lemma 17, the comparison advertised as
strict becomes equality at the central specialization `i=3`. Sections 6--8
give an independent exact equality exclusion, so the candidate proof does
not rely on that strict step.

`DEFINITION`: this observation does not modify the frozen literature pack.
It narrows the permitted wording: even if both Referees accept the proof, no
novelty, priority, `WORLD_FIRST`, or global-absence claim is authorized.

```text
FIRST_UNCERTAIN_MATHEMATICAL_STEP: NONE_WITHIN_FROZEN_DEPENDENCIES
UNRESOLVED_MATHEMATICAL_DEPENDENCIES: NONE
REFEREE_STATUS: NOT_YET_RUN
STRONGER_BOUND_ATTEMPT: NOT_RUN
```
