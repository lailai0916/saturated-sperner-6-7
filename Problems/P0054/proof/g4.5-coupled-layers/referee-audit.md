# P0054 G4.5 referee audit

```text
CURRENT_GATE: P0054_G4_5_COUPLED_LAYER_EQUALITY
VERDICT: ACCEPT
SCOPE: arbitrary finite trace ground set U
NETWORK: OFFLINE
```

## 1. Verdict

`PROVED`: the candidate's deduction from the frozen G4--G4.4 inputs is sound:

```text
|A_3| >= 10,
|F| >= 1+6+12+10+12+6+1 = 48.
```

Thus the canonical total 47 equality profile is excluded. This audit does not
promote a claims entry or determine the exact value of `sat(7)`.

The decisive observation is local to `A_3`; no equality-case classification
for the twelve-member `A_2` or `A_4` blocker pairs is required. The additional
predecessor/successor coupling lemmas in `candidate-proof.md` are valid but
logically optional for the 48 bound.

## 2. Reconstruction of the layer-to-blocker reduction

For an internal layer, write small members as `S subseteq U` and a large
member as `K union H`; put `C=U\K`. The frozen all-or-none and saturated-
antichain hypotheses imply, for every `R subseteq U`,

```text
some S satisfies S subseteq R,
or some C satisfies C intersect R = empty.                    (2.1)
```

The same-layer antichain gives `S intersect C != empty`. Therefore every
small member is a transversal of the `C` family, and every `C` member is a
transversal of the small family.

`PROVED`: the first blocker equality follows directly. A transversal `T` of
the `C` family cannot trigger the second alternative in (2.1), so it contains
a small member. A small member cannot have a proper transversal subset,
because (2.1) would then produce a strictly smaller same-layer small member.

`PROVED`: the second equality needs the complement argument and is valid. For
any transversal `T` of the small family, set `R=U\T`. No small member is
contained in `R`, so (2.1) gives `C subseteq T`. Hence every transversal
contains a `C` member. If a proper subset of a `C` member were a transversal,
it would contain a strictly smaller `C` member, contradicting the `C`
clutter property. Thus the two sides are mutual blockers.

The nonempty-side boundary is covered by `R=empty` and `R=U` together with
the positive middle-layer size bounds. The private-witness injection gives
`|T| <= |G|` for every `T in B(G)`, so the two sides of `A_3` each have at
least three members and transversal number at least three.

## 3. Three-row lemma audit

`PROVED`: if a three-member clutter has all rows of size at least three and
transversal number at least three, the rows are pairwise disjoint. An
intersection point of two rows plus any point of the third row is a
transversal of size at most two. Consequently every blocker chooses exactly
one point from each row, giving at least `3^3=27` blockers.

The argument includes the boundary where the chosen point from the third row
equals the intersection point: then the transversal is a singleton, which is
also prohibited.

## 4. Four-row lemma audit

Let `J` be the intersection graph of four rows. Two vertex-disjoint graph
edges produce two intersection points (possibly the same point), hence a
transversal of size at most two. Therefore the matching number of `J` is at
most one.

The complete graph case split is:

| graph shape | lower-bound mechanism |
|---|---|
| at least two isolated vertices | disjoint-component factorization gives at least `3*3=9` blockers |
| exactly one isolated vertex | the other three rows have `tau>=2`; their blocker cannot be a singleton (blocker involution would force singleton rows), so at least `2*3=6` blockers |
| no isolated vertices | the graph is `K_{1,3}`; the center/leaf incidence count gives at least 9 blockers when the center has no exclusive point and at least 27 otherwise |

For the star, with `p_i=|L_i\E_0|`, `q_i=|L_i intersect E_0|`, and
`c=|E_0\(L_1 union L_2 union L_3)|`, the explicitly minimal sets counted are

```text
prod_i(p_i+q_i) - prod_i p_i + c*prod_i p_i.               (4.1)
```

The first class consists of one point per leaf with at least one center point;
the second consists of one outside-center point per leaf plus a center-only
point. Leaf deletion supplies private witnesses for the second class, and
`tau>=3` makes every first-class three-set minimal. If `c=0`, selecting a
center point from any fixed leaf gives the subcount
`q_i*prod_{j!=i}|L_j| >= 9`.

This exhausts all graph shapes. The first invalid step of a tempting
five-row extension is preserved in `middle-layer-nine-exclusion.md`: matching
number need not be at most one for five rows.

## 5. Equality split audit

With `a=|S_3|`, `b=|C_3|`, the private-witness bounds give `a,b>=3`. If
`a+b=9`, the only splits are

```text
(3,6), (4,5), (5,4), (6,3).
```

The three-row lemma rules out the two splits having a side of size three,
because the opposite blocker side would have at least 27 members. The
four-row lemma rules out the two splits having a side of size four, because
the opposite blocker side would have at least six members. Hence `A_3=9` is
impossible, and the frozen `A_3>=9` bound strengthens to `A_3>=10`.

## 6. Exact checks and evidence boundary

`COMPUTED`: the repository's independent powerset and choice-union blocker
validators agree on all 199 labelled clutters on ground sizes `0,1,2,3,4`,
including empty-family and empty-row boundaries. The incidence formula agrees
on the 194 nonempty-family cases.

`COMPUTED`: the G4.5 checker exhausts labelled three- and four-row clutters
with row sizes at least three for ground sizes `3,4,5,6`; no such small ground
set has transversal number at least three. Its two validators also check the
non-vacuous examples with blocker counts `27`, `19`, and `21`. The finite
checks are regression evidence only and are not used in the arbitrary-finite
proof.

`UNKNOWN`: exact `m(3,3)`, exact `sat(7)`, novelty, and priority. The mandatory
Lean and `uv` repository suites remain environment-blocked in this clone when
the pinned toolchains are unavailable offline; that does not affect the
dependency-closed combinatorial argument.

```text
FIRST_INVALID_STEP: assuming the five-row intersection graph has matching
number at most one
MATHEMATICAL_VERDICT: ACCEPT
CLAIMS_OR_STATUS_MODIFIED: NO
```
