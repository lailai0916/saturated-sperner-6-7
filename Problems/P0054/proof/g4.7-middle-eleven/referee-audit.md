# P0054 G4.7 referee audit

```text
CURRENT_GATE: P0054_G4_7_MIDDLE_LAYER_TOTAL_ELEVEN
REVIEWED_COMMIT: 03484ce
VERDICT: ACCEPT
SCOPE: arbitrary finite trace ground set U
NETWORK: OFFLINE
```

## 1. Verdict

`PROVED`: the candidate's deduction from the frozen G4--G4.6 inputs is sound:

```text
m(3,3) >= 12,
|A_3| >= 12,
|F| >= 1+6+12+12+12+6+1 = 50.
```

Thus a middle layer of total size eleven is impossible. This audit does not
promote a claims entry or determine exact `m(3,3)` or exact `sat(7)`.

Every frozen input hash in `frozen-subproblem.md` matches the reviewed
checkout.

## 2. Residual-family lemma

`PROVED`: the residual family need not remain a clutter. Taking its
inclusion-minimal rows gives a finite nonempty clutter `K` with the same
transversals and blocker.

When at most two points are deleted, every residual row remains nonempty. An
inclusion-minimal residual transversal avoids the deleted points and remains
minimal for the original family, because its subsets meet an original row
exactly when they meet that residual row.

After deleting one point, every residual row has size at least two. If the
residual blocker had a unique member `T`, finite blocker involution would give

```text
K=B(B(K))=B({T})={{x}:x in T}.
```

This would make every member of `K` a singleton, contradicting the residual
row-size bound. Hence there are at least two residual blockers.

## 3. Five-member lemma

The accepted G4.6 high-incidence and matching-number-zero-or-one cases already
give at least nine blockers. It remains only to audit matching number two in
the loop-multigraph model, where actual points retain their multiplicity.

For every actual two-edge matching `M`, the generated family `F_M` contains at
least three minimal three-point edge covers.

- If a second actual matching `N` shares no actual point with `M`, the two
  generated families are disjoint and give at least six blockers. Deleting one
  selected point from each matching produces another blocker outside both
  families.
- If `M={e,f}` and `N={e,g}`, parallel `f,g` give disjoint generated families.
  Otherwise their supports are different two-subsets of the three vertices
  outside `e`, and the generated families intersect in at most `{e,f,g}`.
  Deleting `e` gives at least two blockers outside both generated families, so
  the total is at least seven.
- If `M` is the unique actual matching, every point incident with its unmatched
  vertex is a loop. The other four rows form a disjoint clutter `K` with row
  sizes at least three. Blocker involution and the private-witness injection
  give `|B(K)|>=3`; component factorization then gives at least `3*3=9`
  blockers.

The argument retains loops, parallel actual points, repeated supports,
inactive points, nonuniform row sizes, and arbitrary finite ground sets.
Consequently every five-member clutter with row size and transversal number at
least three has at least seven blockers.

## 4. Local and global deduction

For a mutual-blocker pair of total size at most eleven, exchange the sides so
the smaller side has size `a`. The private-witness bounds give `a>=3`, while
`a<=5`. The three-, four-, and strengthened five-member lemmas give opposite
side bounds

```text
27, 9, 7,
```

respectively. Every split contradicts total size at most eleven, proving
`m(3,3)>=12`.

The frozen middle-layer interface and other-layer bounds then give the
candidate global consequence `sat(7)>=50` in the eventual-stability reduction.

## 5. Evidence boundary

`COMPUTED`: the frozen G4.6 `(5,6)` zero hit is regression evidence only and
is not a dependency of the arbitrary-finite proof.

`UNKNOWN`: exact `m(3,3)`, exact `sat(7)`, existence of a twelve-member local
pair, compatibility of equality across adjacent layers, novelty, and priority.

```text
FIRST_INVALID_STEP: NONE
MATHEMATICAL_VERDICT: ACCEPT
CLAIMS_OR_STATUS_MODIFIED: NO
```
