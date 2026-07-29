# P0054 G4.13 scratch: pair-graph proof supplement v4

```text
STATUS: PROVED_CANDIDATE_PAIR_GRAPH_CLOSURE_PLUS_COMPUTED_CROSSCHECKS
SCOPE: UNPROMOTED_G4_13_FIVE_ROW_DEGREE_THREE_PAIR_GRAPH_BRANCH
RESULT: ALL_FIVE_THREE_EDGE_PAIR_GRAPHS_EXCLUDED_AT_PROVED_CANDIDATE_LEVEL
FORMAL_GLOBAL_STATUS: UNCHANGED_BY_THIS_SUPPLEMENT
NETWORK: MATHEMATICS_OFFLINE
PROTECTED_FILES_MODIFIED: NO
```

This supplement consolidates the current G4.13 pair-graph branch. It also
records four referee issues found and repaired during the audit.

The statement proved here is a candidate sublemma inside the unpromoted
`sat(7)=55` chain. It is not, by itself, a formal proof of that equality.
The protected project result and global interval remain unchanged.

## Branch reduction

The five-row pair lemma forces exactly three pair blockers in the surviving
degree-three kernel. Their simple graph has exactly one of five isomorphism
types:

```text
P4, P3+K2, 3K2, K3, K1,3.
```

The current proof status is:

| Pair graph | Status | Primary obstruction |
|:---:|:---:|:---|
| `P4` | `PROVED_CANDIDATE` | Generalized three-row trace lemma |
| `P3+K2` | `PROVED_CANDIDATE` | Nine projections, two-row fan, normal forms, degree pressure, blocker closure |
| `3K2` | `PROVED_CANDIDATE` | Partition/cube classification, row witness, persistent pointwise support elimination |
| `K3` | `PROVED_CANDIDATE` | At least 10 endpoint incidences versus degree sum at most 9 |
| `K1,3` | `PROVED_CANDIDATE` | Delete the saturated center and apply residual Lemma 2 |

Thus every simple three-edge pair graph is excluded within the stated branch.

## P3+K2 chain

The current route is entirely structural at the candidate-proof level:

```text
endpoint support classification
  -> 9 projection orbits
  -> 7 classes excluded by the repaired path-endpoint two-row lemma
  -> 2 parallel classes
  -> 32+5 minimal pair-legal normal forms
  -> 24+3 forms excluded by endpoint-degree pressure
  -> 8+2 residual forms excluded by blocker/kernel arguments.
```

### Projection classification

Each fixed pair has support type `D` or `I`. The avoidance-intersection lemma
gives five path types. Coupling the independent edge gives five `D` orbits
and four `I` orbits. Hence there are exactly nine endpoint projections.

The independent orbit replay finds 1800 labelled legal tuples and nine
orbits. Its orbit sizes sum to 1800, and its representative list matches the
hand classification exactly. The old count `8500` describes a different,
historical checker stage and is not used as a count of these tuples.

### Seven-class exclusion

The repaired path-endpoint lemma handles classes 2, 3, 4, 6, 7, 8, and 9.
If path endpoint `x` misses rows `P,Q`, then any point in both full rows,
other than `p`, would form an extra pair blocker with `x`. Therefore the full
intersection is `P intersection Q={p}`, not merely the endpoint intersection.

The two differences `P minus {p}` and `Q minus {p}` each have size at least
two. At most one of their four cross pairs is the fixed pair `{u,v}`. Each of
the other three cross pairs yields a minimal blocker containing `x`. Together
with `{x,p}`, this forces `d(x)>=4`.

Classes 1 and 5 are the only survivors.

### Minimal normal forms

In class 1, rows `R0,R1` have equal endpoint parts. Minimality forces exactly
one left witness and one right witness. A separate row-3 witness occurs only
when neither side witness covers that row. Individual and pair legality leave
14 two-point and 18 three-point completions.

In class 5, the only endpoint inclusions are `R0` and `R2` inside `R4`.
Their private witnesses are either one combined support or two separate
supports. This gives one one-point and four two-point completions.

Repeated supports cannot occur in a minimal completion. Deleting one of two
support twins preserves every row-size and incomparability witness. Hence the
exhaustive subset replay also covers arbitrary finite support multisets.

The replay scans all `2^16=65536` and `2^14=16384` support subsets. It finds
exactly 32 and 5 minimal completions, with no larger completion and no hidden
both-side witness.

### Endpoint pressure and residue

Three structural pressure mechanisms exclude 24 of the 32 class-1 forms and
3 of the 5 class-5 forms:

- two special witnesses add two blockers through central endpoint `p`;
- a path-endpoint fan adds three blockers through `a` or `q`;
- an independent-edge fan adds three blockers through `u` or `v`.

The remaining ten forms are closed as follows:

- nine forms violate the degree bound through the twin endpoint amplifier;
- the last `[1,4]` form is a seven-blocker kernel closed under every restored
  support of rank at most three.

The old 143-completion and 11121-extension tables remain cross-checks only.

## 3K2 chain

Each fixed pair again has type `D` or `I`.

If at least one pair has type `I`, all type-`I` pairs share one common row.
Deleting that row gives three orthogonal `2+2` partitions of four rows. The
number of type-`I` pairs determines three projection classes.

If all pairs have type `D`, rows are words in the 3-cube. The missing words
form an independent set. Its size gives exactly two classes: a duplicated
parity projection and one asymmetric projection.

The four saturated classes have seven endpoint-only blockers. One row-witness
lemma excludes all four without outside-support enumeration. The asymmetric
class is closed pointwise after restricting to one outside point and proving
that every resulting blocker persists when other outside points are restored:

- every outside support except `{R4}` immediately raises a saturated endpoint
  degree or creates an extra pair blocker;
- one `{R4}` point leaves only seven blockers;
- two `{R4}` points force degree four.

The old 125000 endpoint assignments and both 11-orbit support tables remain
cross-checks only.

## Other pair graphs

The `P4` branch follows from the generalized three-row trace lemma in
`p0054_g413_p4_eight_blocker_lemma_v3.md`.

For `K3`, each of five dual rows meets all three graph edges. Each row contains
at least two triangle endpoints. The endpoint incidence sum is therefore at
least 10, while the degree-three bound makes it at most 9.

For `K1,3`, the center already has degree three in the blocker family. Delete
it from the five dual rows and minimize. The residual has five blockers of
size at least three, but residual Lemma 2 forces at least six.

## Referee repairs

This audit repaired four hidden assumptions.

1. The path-endpoint lemma now proves the intersection of the full rows,
   rather than silently promoting an endpoint-projection intersection;
2. the normal-form audit now excludes repeated support twins before its
   exhaustive subset claim;
3. the pair-endpoint lemma now states the five-blocker hypothesis used by its
   degree-three corollary;
4. the asymmetric `3K2` argument now proves blocker persistence before using
   one-point support elimination in a full clutter with many outside points.

The earlier v2 header also used `G4.12_REFEREE_ACCEPTED_sat(7)=55` as its base
status. This supplement does not inherit that wording. The equality remains
an unpromoted candidate chain until the full proof is integrated and passes
the protected project gates.

## Live cross-check

The following six replay scripts all exited with code 0 in this audit:

```text
p0054_g413_p3k2_projection_orbit_audit_v1.js
p0054_g413_p3k2_upstream_lemma_audit_v1.js
p0054_g413_p3k2_normal_form_audit_v1.js
p0054_g413_p3k2_endpoint_structural_classifier_v1.js
p0054_g413_3k2_saturated_row_witness_audit_v1.js
p0054_g413_3k2_all_d_audit_v1.js
```

Key exact results are:

```text
P3+K2 projection orbits:       9 from 1800 labelled tuples
P3+K2 upstream class map:      7 excluded, 2 surviving
P3+K2 minimal normal forms:    32 and 5
P3+K2 endpoint-pressure split: 24+8 and 3+2
P3+K2 residual forms:          10 structurally excluded
3K2 projection classes:        5
3K2 saturated classes:         4 structurally excluded
3K2 asymmetric legal supports: 1, namely {R4}
mismatches:                    0
```

## Supporting hashes

```text
five_row_pair_lemma_v5.md=72166032445a20bf6bc0ed889b21421702ecd8b8b5ea9d85461db3cb8b869334
pair_endpoint_lemma_v2.md=47977370d6e76ffc7d9386f74d930115a079eda5eab7bf00badbc45f04c2ca5d
p4_eight_blocker_lemma_v3.md=bd1eec79e0007269805ad1ec4a52be3501c36f703175e3f2a24e800967cfc06b
remaining_pair_graphs_v2.md=74730c29837daed122efd224edb212c9c84b235b00d0033d251c929f62f26dd7
p3k2_projection_orbit_audit_v1.md=4673ecdce8bc9f986048786161d552fd05aabd292265c25916fbe4fdf7f095ff
p3k2_upstream_lemma_audit_v1.md=e653d5a366b907aa1c659b783caf23e027f7fc8883f3d75d160bcb37e75d4ed1
p3k2_normal_form_audit_v1.md=ce25131fc7ad2e1e4fd304ca3ea4fd0e696143806d23e91a5b25cda2cef39814
p3k2_endpoint_structural_classifier_v1.md=169d427d7e2c6a517ce068bd6fb6d60a5a3d68a0e19963de36a4ad3d6123e9bf
p3k2_residue_structural_closure_v1.md=c715f52073b9884023a8b479c31c127e107b098d3c903f69c9213b6c978bd843
3k2_pure_projection_v4.md=b859137865547ef3b555d1b2594e26b3442da99cd6ca324705e83126f09be500
3k2_saturated_row_witness_audit_v1.md=e595522f7edbe8fa10094765265586b004c6d29381828246b78a903feec51cb9
3k2_all_d_audit_v1.md=faefa9dbad94351c90601f4ff70eab520a7f9fa56ced3a43758bb1cac35fb4b5
residual_lemmas_v3.md=913d35e7100b57d5c0d0e5a0e5ca165c9610daf8f2b507ee485455309f845071
```

## Remaining boundary

The pair-graph subproblem is now closed at the `PROVED_CANDIDATE` level. The
foundational five-row, endpoint, and P4 audits are complete. The remaining
work is integration into the full G4.12/G4.13 chain and protected-gate review.
Until that work passes:

- do not state `sat(7)=55` as a formal theorem;
- do not promote computation to proof;
- do not claim novelty or publication readiness;
- do not modify protected claims or status files.
