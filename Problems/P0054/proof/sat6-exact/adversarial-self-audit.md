# Adversarial self-audit of the exact sat(6) proof

```text
ROLE: AUTHOR_SIDE_ADVERSARIAL_SELF_AUDIT
INDEPENDENT_REFEREE: NO
RESULT: PASS_WITH_EXTERNAL_REVIEW_PENDING
CRITICAL_GAP_FOUND: NO
```

This is an author-side attack on the proof. It is not an independent referee
report and does not satisfy the repository's human-review boundary.

## Audited dependencies

1. The target is the eventual stable number `sat(6)`, not one finite-ground
   value. The proof chooses `n` after stability has begun and also requires
   `n>=8` and `n>2^30`.
2. Morrison--Noel--Scott Proposition 20 gives a 30-member construction on
   every such ground set. Hence a minimum family has at most 30 members, and
   `n>2^|F|` follows without using the desired lower bound.
3. Endpoint normalization is an existence statement for a minimum family.
   The proof chooses that representative; it does not assert that every
   minimum family contains both endpoints.
4. The version-of-record homogeneous threshold is `|H|>=2`. This is enough to
   choose a nonempty proper subset of `H` in the mixed-set saturation argument.
5. The canonical decomposition supplies six pairwise disjoint nonempty
   saturated antichains. Proposition 14 and Lemma 15 are used only under their
   minimum-family and homogeneous-atom hypotheses.

## Local blocker theorem

The following failure modes were tested directly against the proof.

- **Infinite-set leakage:** every ground set is finite. Every transversal
  contains a minimal transversal, and every complement argument remains
  finite.
- **Inactive points:** deleting points outside every row changes no
  transversal or blocker. The theorem itself allows them.
- **Multiset leakage:** all objects are ordinary set families. Repeated point
  incidence patterns are allowed, but duplicate rows are not counted twice.
- **Empty sides:** the member-size hypotheses and blocker equalities force
  both families to be nonempty.
- **Blocker involution:** both inclusions use the clutter hypothesis. The
  complement of a proper subset contains a minimal transversal disjoint from
  that subset.
- **Private-witness injection:** distinct points of a minimal transversal
  receive distinct witness rows, so the cardinality inequalities have the
  correct direction.
- **Three-row count:** the absence of singleton blockers removes the triple
  intersection. The six remaining active incidence classes are exhaustive.
  The formula counts each two- or three-point minimal transversal once. The
  possible equality value six is excluded; the `p_i<=1` cases give minima
  27, 15, 9, and 7.
- **Four-row classification:** two vertex-disjoint intersection edges would
  give a transversal of size at most two. A four-vertex graph with matching
  number at most one is covered by the isolated-component cases or the
  three-leaf star. Blockers factor only across genuinely disjoint active
  components. The star count is at least seven, while the one-isolate case
  gives at least six.
- **Cardinality exhaustion:** the private-witness bounds give
  `a>=3` and `b>=2`. The cases `b=2`, `b=3`, `b>=4,a=3`,
  `b>=4,a=4`, and `b>=4,a>=5` cover every ordered integer pair.
- **Upper witness:** both blocker equalities are proved. Lean and two direct
  finite validators agree that the displayed sides have cardinalities five
  and four and member-size minima two and three.

No finite search result is used in the local proof.

## Global transfer

For the second canonical layer, small traces have size at least two and the
complements of large traces have size at least three. Saturation on a mixed
subset of the homogeneous atom gives the oriented cover condition. The
antichain condition gives cross-intersection, and the two recognition
directions establish mutual blocker equality.

For the third layer, the size minima are reversed. Exchanging the two blocker
sides applies the same local theorem; no complement symmetry of the original
family is assumed. Together with the endpoint and adjacent-layer bounds, the
six layer sizes are at least `(1,5,9,9,5,1)`, whose sum is 30.

## Mechanical evidence

- `COMPUTED`: incidence-pattern enumeration exhausts every ordered split of
  total at most eight and verifies a total-nine witness.
- `FORMALIZED`: Lean proves the arbitrary-finite-ground local lower bound and
  the explicit witness in both blocker directions.
- `PROVED + LITERATURE`: the canonical-layer reduction and final stable-number
  theorem remain a natural-language proof with cited structural inputs.

The local Lean theorem must not be described as a full Lean formalization of
`sat(6)=30`.

## Findings

One typographical defect was found in the final sum: `|F|ge` was corrected to
`|F|\ge`. No mathematical dependency changed.

Novelty and priority remain `UNKNOWN`. A specialist should independently
reconstruct the local counting lemmas and verify the source-to-theorem
crosswalk before public submission.
