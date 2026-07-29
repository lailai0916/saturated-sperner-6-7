# P0054 G4 Prover A: canonical decomposition and endpoint audit

```text
ROLE: COMPATIBILITY_OFFLINE_ISOLATED_PROVER_A
NETWORK: FORBIDDEN; NOT_USED
OTHER_G4_ATTEMPTS_READ: NO
EXPERIMENT_REPORT_READ: NO
FORMALIZER_USED: NO
SCOPE: eventual sat(7) -> minimum family -> homogeneous atom -> canonical layers -> endpoint bounds
GLOBAL_LOWER_BOUND_PROVED_HERE: NONE
FIRST_UNCERTAIN_STEP: NONE
FIRST_FAILED_LITERAL_STEP: PHASE_2_ITEM_3_LAYERWISE_ATOM_MAXIMALITY
FIRST_FAILED_LITERAL_STEP_STATUS: REFUTED
```

## 0. Frozen inputs and evidence boundary

`COMPUTED`: the frozen literature inputs read by this Prover had the following
SHA-256 values:

```text
dc4a5258ce5fc4b4d2d2ffa5aeb6d96b51d467b2cf013c1655ca44486d22497c  literature-pack.md
fee4fddb9bc0f25cc017e23b2bd7366db9687307c2686270ffa6ff408a20ede0  source-theorem-matrix.md
62313da89a38e1a773954956c8252bf7afcd2e841842bc7686a8fd39cae4a62d  freeze-manifest.json
```

`COMPUTED`: the first two values agree with the corresponding entries in
`freeze-manifest.json`. The manifest also records the search cutoff as
`2026-07-22T08:55:25-07:00` and forbids network use after the freeze. This
Prover did not use the network.

`LITERATURE`: this audit takes only the following results from the frozen pack:

1. for fixed `k`, `sat(n,k)` is eventually constant;
2. when `2 <= k <= n`, a minimum-cardinality saturated `k`-Sperner family may
   be chosen to contain both endpoints (Gerbner et al. 2013, Lemma 6 as routed
   by the frozen matrix);
3. if `|X| > 2^|F|`, the saturated family `F` has a homogeneous atom, and a
   saturated family cannot have two distinct homogeneous atoms
   (Martin--Veldt 2025, Lemma 6);
4. the iterative inclusion-minimal canonical decomposition is the one in
   Martin--Veldt Definitions 9--10 / MNS Definition 12;
5. if a saturated `k`-Sperner family has a homogeneous atom `H`, every
   canonical layer is a saturated antichain (Martin--Veldt Lemma 13 / MNS
   Lemma 17);
6. Martin--Veldt Proposition 14 supplies the small/large size restrictions in
   the endpoint-normal minimum-family setup, and Lemma 15 supplies the first
   and last internal-layer bounds.

`PROVED`: the existing repository claim `P0054-C7`, `sat(7) <= 55`, is used
only to select a ground set large enough for the atom theorem. No proposed G4
lower bound is used in this selection.

`DEFINITION`: throughout this file, **minimum family** means one of minimum
cardinality among all saturated families on the fixed ground set. An
**inclusion-minimal member** is a set with no strict subset in the current
remainder. These are different notions. The canonical decomposition uses the
second notion; endpoint normalization and Martin--Veldt Lemma 15 use the
first.

## 1. Exact theorem established by this route

### Theorem A (corrected canonical endpoint package)

`PROVED` relative to the six frozen `LITERATURE` inputs above:

There is a stabilization threshold `N_stab` such that, for every integer `n`
with

```text
n >= N_stab,   n >= 7,   and   n > 2^55,
```

one may choose an `n`-element set `X`, a minimum-cardinality saturated
7-Sperner family `F` on `X`, and a homogeneous atom `H` of `F` so that all of
the following hold.

1. `|F| = sat(n,7) = sat(7) <= 55`.
2. `empty in F` and `X in F`.
3. The VOR-compatible atom has `|H| >= 2`.
4. If `A_0,A_1,...` is the canonical decomposition, then precisely
   `A_0,...,A_6` are nonempty, they are pairwise disjoint, and their union is
   `F`.
5. Every `A_i`, `0 <= i <= 6`, is a saturated antichain.
6. The same set `H` is an all-or-none block for every `A_i`: each member of
   each layer either contains all of `H` or is disjoint from `H`.
7. `A_0={empty}` and `A_6={X}`.
8. `|A_1| >= 6` and `|A_5| >= 6`.

The stronger literal statement that the same `H` is a homogeneous **atom**
of every layer is false when atom includes maximality. It must be replaced by
item 6. This correction does not weaken the saturated-antichain conclusion.

## 2. Stable ground-set and minimum-family quantifiers

`PROVED`: eventual stability supplies an integer `N_stab` such that

```text
sat(n,7) = sat(7)  for every n >= N_stab.
```

Choose `n` satisfying the three inequalities in Theorem A. This is legitimate
because they are finitely many lower thresholds on an integer. On an
`n`-element ground set there are finitely many set families, so the minimum in
`sat(n,7)` is attained.

`PROVED`: endpoint normalization is an existential selection statement, not
a universal property of all minimum families. Since `2 <= 7 <= n`, the frozen
Gerbner-et-al. input permits choosing a minimum family `F` with both `empty`
and `X` in `F`. The replacement does not increase cardinality; because the
starting cardinality was already the minimum, the selected family is still
minimum and

```text
|F| = sat(n,7) = sat(7) <= 55.
```

The order of operations matters: choose an endpoint-normal minimum family,
then apply the atom theorem to that selected family. No claim is made that an
arbitrary previously chosen minimum family already contains the endpoints.

`PROVED`: from `|F| <= 55`, monotonicity of integer exponentiation gives

```text
2^|F| <= 2^55 < n = |X|.
```

Martin--Veldt Lemma 6 therefore supplies a homogeneous atom `H` of this same
family `F`. This is not circular: the only numerical input is the already
proved upper bound `sat(7) <= 55`, not the candidate lower bound 37 or any
internal-layer estimate.

### The `|H|=2` boundary

`LITERATURE`: the binding frozen G4 pack records that the actual
Martin--Veldt VOR defines a homogeneous atom using `|H| >= 2`. Older local
P0053 materials transcribed the threshold as `|H|>2`; those older files are
not silently rewritten here.

`PROVED`: every argument in Sections 3--6 below is valid at `|H|=2`.
Inheritance of all-or-none blockness only needs `H` to exist. Distinguishing a
small member from a large member only needs `H` to be nonempty. The frozen
Martin--Veldt Lemmas 13 and 15 are invoked with their VOR-compatible
homogeneous-atom hypothesis. If one directly needs a partial intersection of
`H`, either singleton of a two-element `H` is a nonempty proper subset. Thus
there is no hidden upgrade to `|H|>2` in this audit.

## 3. Seven and only seven nonempty canonical layers

`DEFINITION`: let `R_0=F`. For every `i>=0`, let `A_i` be the
inclusion-minimal members of `R_i`, and put `R_(i+1)=R_i\A_i`.

`PROVED`: each `A_i` is an antichain. Two distinct inclusion-minimal members
of the same remainder cannot strictly contain one another.

`PROVED`: distinct canonical layers are disjoint, because a member removed in
`A_i` does not occur in any later remainder.

`PROVED`: if `R_i` is nonempty, then `A_i` is nonempty. The family `R_i` is
finite, so choosing a member of minimum set-cardinality gives an
inclusion-minimal member. This is a local finite-poset argument and does not
use minimum cardinality of `F` among saturated families.

`PROVED`: every member of `A_(i+1)` strictly contains a member of `A_i`.
Indeed, for `D in A_(i+1)`, choose an inclusion-minimal member `C` of `R_i`
with `C subseteq D`; such a `C` exists by descending inside the finite set of
members of `R_i` contained in `D`. Then `C in A_i`. Equality would put `D` in
`A_i`, although `D in R_(i+1)`, so `C proper_subset D`.

`PROVED`: `R_7` is empty. Otherwise `A_7` is nonempty. Starting at a member of
`A_7` and applying the preceding strict-predecessor statement seven times
would give eight members of `F` in a strict chain, contradicting that `F` is
7-Sperner. Consequently

```text
F = A_0 union A_1 union ... union A_6,
```

and every layer with index at least seven is empty.

`PROVED`: there is a strict seven-member chain in `F`. Since `|F|<=55` while
`|P(X)|=2^n>55`, choose `S subseteq X` outside `F`. Saturation says that
`F union {S}` contains a strict eight-member chain. The chain must use `S`,
because `F` itself is 7-Sperner. Removing `S` leaves seven members of `F` in
strict order.

`PROVED`: a strict containment from a member of `A_i` to a member of `A_j`
forces `i<j`. If instead `j<=i`, the lower set is still present in remainder
`R_j`, contradicting inclusion-minimality of the upper set in `R_j`.
Therefore the seven members of the preceding chain have seven strictly
increasing layer indices among `0,...,6`; their indices are exactly
`0,1,...,6`. Every one of these seven layers is nonempty.

This proves “exactly seven nonempty layers” without assuming nonemptiness as
part of the canonical-decomposition definition.

## 4. Saturation of each layer and the common-atom mismatch

`LITERATURE`: Martin--Veldt Lemma 13 / MNS Lemma 17 states that if a saturated
`k`-Sperner family has a homogeneous atom `H`, each canonical layer is a
saturated antichain. The theorem has no minimum-cardinality hypothesis.

`PROVED`: applying that source theorem to `F,H,k=7` gives that each
`A_i`, `0<=i<=6`, is a saturated antichain. The antichain half also follows
directly from Section 3; the cited result supplies maximality/saturation in
the whole Boolean lattice `P(X)`.

`PROVED`: since `A_i subseteq F`, the all-or-none property of `H` in `F`
restricts to every layer. Thus the same `H` is a common all-or-none block for
all seven layers. This inherited property has the quantifier order

```text
there exists H such that for every i and every B in A_i,
either H subseteq B or B is disjoint from H.
```

It is not a sequence of unrelated layer-dependent blocks.

`REFUTED`: maximality of an atom does not in general pass from a family to a
subfamily, and here it definitely fails at both endpoints. Section 5 proves
`A_0={empty}` and `A_6={X}`. For either singleton family, every subset of `X`
has the all-or-none property, so its unique maximal atom is `X`.

Moreover `H` is a proper subset of `X`. If `H=X`, the all-or-none property for
`F` would force every member of `F` to be either `empty` or `X`, contradicting
the seven-member chain in Section 3. Hence `H` is not an atom of `A_0` or
`A_6`.

Therefore Phase 2 item 3, if “homogeneous atom” retains the source definition
including maximality, is false. The dependency-safe statement is:

```text
every A_i is a saturated antichain, and the same H is an inherited
all-or-none block for every A_i.
```

No later argument may cite this file for layerwise atom maximality. A direct
small/large coverage argument may use the displayed common-block statement
and `|H|>=2`; it does not need maximality of `H` inside an individual layer.

## 5. Exact endpoint layers

`PROVED`: `A_0={empty}`. The empty set is in `F` and is contained in every
member of `F`, so it is inclusion-minimal. Every other member strictly
contains it and therefore is not inclusion-minimal in `F`.

`PROVED`: `A_6={X}`. Let

```text
D_0 proper_subset D_1 proper_subset ... proper_subset D_6
```

be the seven-member chain obtained in Section 3. If `D_0` were not empty,
prepending the member `empty in F` would give an eight-member chain in `F`.
Thus `D_0=empty`. If `D_6` were not `X`, appending the member `X in F` would
give an eight-member chain in `F`. Thus `D_6=X`.

The layer-index argument in Section 3 places `D_i` in `A_i`, hence `X in A_6`.
Since `A_6` is an antichain and every subset of `X` is below `X`, it has no
second member. Therefore `A_6={X}`.

This proof checks both endpoint choices. It does not infer universal endpoint
membership for every minimum family; it uses the endpoint-normal minimum
family selected in Section 2.

## 6. The bounds on `A_1` and `A_5`

`LITERATURE`: under the same endpoint-normal minimum-family, canonical, and
homogeneous-atom hypotheses, Martin--Veldt Lemma 15 says that `A_1` has at
least `k-2` small singleton members and exactly one large member. The lemma
also states the order-dual conclusion for `A_(k-2)`.

`PROVED`: at `k=7`, `A_1` therefore has at least five small singleton members
and one large member. A small member is disjoint from the nonempty `H`; a
large member contains `H`. They are distinct, so

```text
|A_1| >= 5+1 = 6.
```

`PROVED`: the dual conclusion in the same source lemma gives at least five
members of the dual type and one member of the other type in `A_5`. The two
types are disjoint because `H` is nonempty, so

```text
|A_5| >= 5+1 = 6.
```

No complement symmetry of the chosen family is assumed. The second bound is
the source lemma's dual assertion, not an inference that `F` equals its own
complement.

`LITERATURE`: Martin--Veldt Proposition 14 also gives the downstream size
restrictions

```text
|S| >= i                    for every small S in A_i,
|X \ L| >= 7-i-1            for every large L in A_i.
```

This file records that source seam but does not use it for any probabilistic
or internal-layer estimate.

## 7. Boundary-case audit

`PROVED`:

- **Empty layers.** Empty canonical layers were not ruled out by definition.
  They were ruled out for indices `0,...,6` using an actual seven-chain; all
  layers from index seven onward are empty by the 7-Sperner contradiction.
- **External-set existence.** It follows from `2^n>55>=|F|`; saturation was
  not applied to a nonexistent external set.
- **Minimum versus minimal.** Endpoint normalization and Lemma 15 concern a
  minimum-cardinality family. Canonical peeling concerns inclusion-minimal
  members of successive remainders. The two notions are never substituted.
- **The atom threshold.** The binding VOR threshold is `|H|>=2`. No argument
  here needs the older, stronger local transcription `|H|>2`.
- **Endpoint choice.** The proof selects an endpoint-normal minimum family;
  it does not claim every minimum family has both endpoints.
- **Atom maximality.** Only the union family `F` is asserted to have `H` as a
  homogeneous atom. Individual layers inherit blockness, not maximality.
- **Small/large side emptiness.** Lemma 15 itself provides members of both
  types in `A_1` and `A_5`; their lower bounds do not assume either side is
  nonempty before applying the source result.
- **Stable quantifier.** A lower bound proved for the selected minimum family
  at any `n>=N_stab` immediately bounds `sat(7)`, because
  `|F|=sat(n,7)=sat(7)`. One does not need to prove the layer estimates anew
  for every finite `n`, although the construction above works for every `n`
  satisfying the displayed thresholds.

## 8. Dependency list and stopping boundary

```text
D1  eventual stability of sat(n,7)                         LITERATURE
D2  existing sat(7)<=55                                    PROVED (P0054-C7)
D3  endpoint-normal minimum-family selection               LITERATURE
D4  |X|>2^|F| homogeneous-atom theorem                     LITERATURE
D5  canonical decomposition definitions                    DEFINITION
D6  finite-poset peeling, coverage, and seven-layer proof  PROVED here
D7  canonical-layer saturation with atom H                 LITERATURE
D8  inherited common all-or-none block                     PROVED here
D9  exact endpoint layers                                   PROVED here
D10 Martin--Veldt first/last internal-layer lemma           LITERATURE
D11 |A_1|>=6 and |A_5|>=6                                  PROVED here from D10
```

`REFUTED`: the additional dependency “`H` is a maximal homogeneous atom of
every `A_i`” is not available and is false at `A_0,A_6`.

`UNKNOWN`: this route does not address `A_2`, `A_3`, or `A_4`, does not add
the seven layer sizes, and proves no new numerical global lower bound by
itself. In particular it neither proves nor refutes `sat(7)>=37`.

```text
FIRST_UNCERTAIN_STEP: NONE
FIRST_FAILED_LITERAL_STEP: PHASE_2_ITEM_3_LAYERWISE_ATOM_MAXIMALITY
FAILURE_REASON: atom maximality is not hereditary; endpoint layers have atom X, not H
CORRECTED_DEPENDENCY: common H all-or-none block + saturated antichain layers
OPEN_GAPS_WITHIN_ASSIGNED_SCOPE: NONE
STOP_REASON: ASSIGNED_CANONICAL_AND_ENDPOINT_AUDIT_COMPLETE
```
