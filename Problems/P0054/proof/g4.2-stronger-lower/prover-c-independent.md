# P0054 G4.2 — Prover C independent blocker proof

```text
ROLE: PROVER_C_COMPATIBILITY_LAUNCH
ISOLATION: INDEPENDENT_FROM_PROVERS_A_AND_B
NETWORK: NOT_USED
FORMALIZER: NOT_USED
RESULT: PROVED
TARGET: THEOREM_A2_CANDIDATE
EPISTEMIC_STATUS: PROVED_NOT_FORMALIZED
```

## 1. Source and dependency boundary

`DEFINITION`: this report uses only the following frozen inputs.

| Input | SHA-256 checked by Prover C |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/proof/g4.2-stronger-lower/frozen-subproblem.md` | `2149cbed8621e7643307e8c508301d898e25e3a661bc2b1f05910354f2ba2a42` |
| `Problems/P0054/proof/g4-global-lower/candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| `Problems/P0054/experiments/g4.2-stronger-lower/section0-freeze.md` | `6551eda020048d809f5cd9f8d85908cc821a1adc2c9d8c026960354533d9d5d4` |

`DEFINITION`: no output of another G4.2 Prover or Experimentalist is an
input. No old proof, status, claims, certificate, manifest, or Lean file is
modified by this report.

## 2. Exact theorem

`DEFINITION`: let `U` be an arbitrary finite set. Let

```text
S = {S_1,...,S_a} subseteq 2^U
K = {K_1,...,K_b} subseteq 2^U
```

be the small generators and the traces of the large members of one second
internal layer. Put

```text
C_j = U \ K_j,     C = {C_1,...,C_b}.
```

The frozen hypotheses are:

1. `S` and `K` are antichains, hence `C` is an antichain;
2. `|S_i| >= 2` and `|C_j| >= 4`;
3. `S_i` is not contained in `K_j`, equivalently
   `S_i intersect C_j` is nonempty, for every `i,j`;
4. for every `R subseteq U`,

   ```text
   (there exists i with S_i subseteq R)
   or
   (there exists j with R subseteq K_j).
   ```

`PROVED` (`THEOREM_A2_CANDIDATE`): under these hypotheses,

```text
a + b >= 8.
```

In particular, there is no seven-member second internal layer on any finite
`U` satisfying the frozen hypotheses.

## 3. Blocker terminology

`DEFINITION`: a transversal of a set family `H` is a set meeting every
member of `H`. Its blocker `B(H)` is the family of inclusion-minimal
transversals of `H`.

`PROVED` (recognition lemma): suppose `G` is an antichain, every member of
`G` is a transversal of `H`, and every transversal of `H` contains a member
of `G`. Then `G = B(H)`.

Proof. Let `G_0` belong to `G`. If a proper subset `D` of `G_0` were a
transversal of `H`, the containment hypothesis would give some
`G_1 in G` with

```text
G_1 subseteq D proper-subset G_0,
```

contradicting the antichain property. Thus `G_0` is a minimal transversal.
Conversely, if `T` is a minimal transversal, it contains some `G_0 in G`;
because `G_0` is itself a transversal, minimality gives `T=G_0`. This proves
the lemma.

## 4. The two layer sides are exact blockers

`PROVED`: both `S` and `C` are nonempty. If `C` were empty, the covering
condition at `R=empty` would fail because no `S_i` of size at least two is
contained in `empty`. If `S` were empty, the covering condition at `R=U`
would fail because `U` is not contained in any `K_j=U\C_j` with
`|C_j|>=4`.

`PROVED`: `S = B(C)`. Every `S_i` meets every `C_j` by the cross-antichain
condition, so every `S_i` is a transversal of `C`. If `R` is any transversal
of `C`, then `R` is not contained in any `K_j=U\C_j`. The covering condition
therefore forces `S_i subseteq R` for some `i`. The recognition lemma applies
because `S` is an antichain.

`PROVED`: `C = B(S)`. Every `C_j` meets every `S_i`, so every `C_j` is a
transversal of `S`. Let `D` be any transversal of `S` and apply the covering
condition to `R=U\D`. No `S_i` is contained in `R`, because `D` meets every
`S_i`. Hence there is a `j` with

```text
U \ D subseteq K_j = U \ C_j,
```

which is equivalent to `C_j subseteq D`. The recognition lemma applies
because `C` is an antichain.

## 5. Private-witness bound

`PROVED` (private-witness lemma): if `T in B(H)` and `x in T`, there exists
an `E_x in H` such that

```text
T intersect E_x = {x}.
```

Indeed, `T\{x}` is not a transversal, so some `E_x` is disjoint from
`T\{x}`; since `T` is a transversal, its intersection with `E_x` is exactly
`{x}`. Distinct elements of `T` require distinct witnesses. Therefore

```text
|T| <= |H|.                                                   (1)
```

`PROVED`: applying (1) to `C_j in B(S)` and to `S_i in B(C)` gives

```text
4 <= |C_j| <= a,     2 <= |S_i| <= b.                         (2)
```

Because both sides are nonempty, (2) implies

```text
a >= 4,     b >= 2.                                           (3)
```

## 6. The case of two large complements

`PROVED`: if `b=2`, then `C_1` and `C_2` are disjoint. Otherwise an element
`x in C_1 intersect C_2` would make `{x}` a minimal transversal of `C`, so
`{x}` would belong to `B(C)=S`, contrary to `|S_i|>=2`.

`PROVED`: when `C_1` and `C_2` are disjoint, every pair

```text
{x,y},     x in C_1, y in C_2,
```

is a minimal transversal of `C`: it meets both complements, and deletion of
either element leaves the other complement unhit. These pairs are distinct,
so

```text
a = |B(C)| >= |C_1| |C_2| >= 4*4 = 16.                       (4)
```

Thus `b=2` gives `a+b>=18` and cannot occur in a seven-member layer.

## 7. The critical case of three large complements

`PROVED`: if `b=3` and `a>=5`, then `a+b>=8`. It remains only to refute
`a=4`. Assume for contradiction that

```text
C = {C_1,C_2,C_3},     S = {S_1,S_2,S_3,S_4}.
```

`PROVED`: every `C_j` then has size exactly four. The lower bound is a
frozen hypothesis, and (1) gives `|C_j|<=a=4`.

`PROVED`: for every fixed `j`, each of the four intersections
`C_j intersect S_i` is a singleton, and these four singleton elements are
pairwise distinct. To see this, apply the private-witness lemma to every
`x in C_j`, viewing `C_j` as a member of `B(S)`. It assigns to `x` some
`S_i` with `C_j intersect S_i={x}`. Two distinct `x` cannot be assigned the
same `S_i`. There are four elements and four `S_i`, so this injection is a
bijection. Consequently every `S_i` occurs as one singleton witness, and
the four witness elements are distinct.

`PROVED`: the sets `S_1,S_2,S_3,S_4` are pairwise disjoint. First, every
element `x in S_i` belongs to some `C_j`: apply the private-witness lemma to
`S_i in B(C)`. If an element belonged to both `S_i` and `S_k`, choose a
`C_j` containing it. The preceding paragraph would then give two equal
singleton intersections in the fixed `C_j`, contradicting their pairwise
distinctness.

`DEFINITION`: for `x in S_i`, define its support among the three large
complements by

```text
I(x) = {j in {1,2,3} : x in C_j}.
```

`PROVED`: for every `i`, the supports `{I(x):x in S_i}` form a nontrivial
partition of `{1,2,3}`. Each support is nonempty because every element of
`S_i` lies in some `C_j`. For each `j`, the singleton-intersection result
says that exactly one element of `S_i` lies in `C_j`, so the supports are
disjoint and cover all three indices. Finally, the partition has at least
two blocks because `|S_i|>=2`. Thus it has type `2+1` or `1+1+1`; no
uniformity between different `S_i` is assumed.

`PROVED` (two-partition lemma): two nontrivial partitions `P,Q` of a
three-element set have an irredundant cover by blocks using at least one
block of `P` and at least one block of `Q`.

Proof. If `P` has a two-element block `A`, let `r` be the remaining point
and let `B` be the block of `Q` containing `r`. Then `A union B` is the
whole three-element set. Both blocks are proper. The point `r` is private
to `B`, while `A` has a point outside `B` because otherwise `B` would be the
whole set. Hence `{A,B}` is irredundant. The same argument with `P,Q`
reversed handles the case in which only `Q` has a two-element block. If
neither has one, both partitions consist of three singletons; take two
singletons from `P` and the remaining singleton from `Q`.

`PROVED`: apply the two-partition lemma to the support partitions belonging
to `S_1` and `S_2`. Replace each selected support block by its corresponding
element of `S_1` or `S_2`, and call the resulting set `T`. The selected
supports cover `{1,2,3}`, so `T` meets every `C_j`. Irredundancy gives each
element of `T` a private `C_j`, so `T` is a minimal transversal of `C`.
Therefore

```text
T in B(C) = S.                                                (5)
```

On the other hand, `T` contains an element of `S_1` and an element of
`S_2`. Since the four `S_i` are pairwise disjoint, `T` equals none of them.
This contradicts (5). Hence `b=3` forces

```text
a >= 5.                                                       (6)
```

## 8. Exhaustion and counterexample verdict

`PROVED`: all possible values of `b` are exhausted as follows.

- `b<=1` is impossible by (3).
- `b=2` gives `a>=16` by (4).
- `b=3` gives `a>=5` by (6).
- `b>=4` together with `a>=4` from (3) gives `a+b>=8`.

Therefore `a+b>=8` in every case. In the requested hypothetical equality
`a+b=7`, (3) first reduces the split to exactly

```text
(a,b)=(5,2) or (a,b)=(4,3).
```

The first split has at least sixteen small blockers, and the second split
has the additional cross-partition blocker constructed in Section 7. Thus
the structural counterexample search is exhaustive and returns no
counterexample.

## 9. Boundary audit

- `PROVED`: arbitrary finite `U` is covered. Finiteness is used only to pass
  to inclusion-minimal transversals. No numerical upper bound on `|U|`
  occurs.
- `PROVED`: elements of `U` outside `union C` cannot occur in a minimal
  transversal in `S`; they otherwise play no role. Hence arbitrarily many
  unused or all-large incidence coordinates do not affect the proof.
- `PROVED`: repeated element-incidence patterns are allowed. The
  private-witness argument counts actual distinct elements. In the critical
  `b=3,a=4` equality case, repeated supports inside one `S_i` are themselves
  excluded by singleton intersections; equal supports in different `S_i`
  remain allowed and do not affect the two-partition construction.
- `PROVED`: nonuniform sizes are covered. In the critical case,
  `|C_j|>4` is already impossible by (1), while each `S_i` may independently
  have size two or three. The two-partition lemma treats both types. In the
  `b=2` case, larger complements only increase the product in (4).
- `PROVED`: empty small or large sides are excluded directly at `R=U` or
  `R=empty`; they are not silently omitted from the split analysis.
- `PROVED`: the families are ordinary set families, not multisets. Distinct
  large layer members give distinct traces and distinct complements;
  complementing reverses containment, so the large-side antichain is exactly
  the antichain condition needed for `C`.
- `PROVED`: the proof uses the covering condition for every `R subseteq U`
  in both orientations: first with an arbitrary transversal of `C`, then
  with the complement of an arbitrary transversal of `S`. It does not replace
  the universal quantifier by a finite sample.
- `PROVED`: all containments in the oriented cover are the required
  non-strict containments. Minimality is introduced only after applying the
  cover to arbitrary transversals.
- `PROVED`: no probability comparison, floating-point arithmetic, finite
  search, or hidden uniformity assumption is used.

## 10. Relationship to P0054-C17 and stopping boundary

`PROVED`: the combinatorial deduction above does not use the numerical
conclusion `|A_2|>=7` from Section 7 of the frozen G4 candidate proof, nor
does it use the resulting global lower bound recorded by the G4/C17 gate.
It uses only the upstream frozen A2 hypotheses: within-side antichains, the
size bounds, the cross-antichain condition, and the universal oriented cover.

`PROVED`: conditional on the remaining layer bounds already displayed in
the frozen G4 candidate proof, replacing its `|A_2|>=7` term by this
`|A_2|>=8` term changes the layer sum arithmetically to

```text
1 + 6 + 8 + 9 + 7 + 6 + 1 = 38.
```

`DEFINITION`: this report does not alter P0054-C17, does not create
P0054-C18, and does not claim that the stronger global bound has passed its
required isolated Referee gate. It is an isolated Prover result only.

```text
FIRST_UNCERTAIN_MATHEMATICAL_STEP: NONE_WITHIN_THE_FROZEN_SUBPROBLEM
EXTERNAL_DEPENDENCY_BOUNDARY: DERIVATION_OF_THE_FROZEN_A2_HYPOTHESES_FROM_THE_GLOBAL_G4_SETTING
COUNTEREXAMPLE_STATUS: NONE; ALL_SEVEN_MEMBER_SPLITS_EXHAUSTED
FORMALIZATION_STATUS: NOT_FORMALIZED
CLAIMS_OR_STATUS_MODIFIED: NO
```
