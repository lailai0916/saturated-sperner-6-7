# P0054 G4.13 scratch: P3+K2 upstream lemma audit v1

```text
STATUS: PROVED_CANDIDATE_REPAIRED_LEMMA_PLUS_COMPUTED_EXACT_MAP
SCOPE: P3+K2_PATH_ENDPOINT_TWO_ROW_LEMMA_AND_SEVEN_CLASS_APPLICATION
RESULT: FULL_ROW_INTERSECTION_GAP_CLOSED; CLASSES_2_3_4_6_7_8_9_EXCLUDED
NETWORK: MATHEMATICS_OFFLINE
```

This note repairs one implicit step in
`p0054_g413_p3k2_upstream_reduction_v1.md`. That note used the endpoint
projection identity `P intersection Q={p}` as though it were already the
intersection of the full rows. The conclusion is valid, but the outside-point
case must be excluded explicitly.

No global bound or protected claim changes here.

## Repaired path-endpoint two-row lemma

Work in the no-singleton, fixed-`P3+K2` pair-blocker branch. Let `x` be one
of the path endpoints `a,q`, with fixed partner `p`. Suppose `x` is absent
from exactly two full rows `P,Q`, while `p` belongs to both, and suppose the
endpoint projections of `P,Q` intersect only at `p`.

Then the full rows satisfy

```text
P intersection Q = {p}.
```

Indeed, let `w` be any other point in both rows. The pair `{x,w}` hits `P,Q`
through `w` and hits each of the other three rows through `x`. Neither point
is a singleton transversal: `x` misses `P,Q`, while singleton blockers are
excluded in this branch. Hence `{x,w}` is a pair blocker. It is not one of
the fixed `P3+K2` edges, a contradiction. This covers both endpoint and
outside choices of `w`.

Since every full row has size at least three, the disjoint sets

```text
P minus {p}, Q minus {p}
```

each have size at least two. They determine at least four distinct cross
pairs `{y,z}`. The only fixed pair blocker avoiding both `x` and `p` is
`{u,v}`, so at most one cross pair is a blocker.

For each of the other at least three cross pairs, `{y,z}` is not a
transversal. Choose a row `H` missing both. It is different from `P,Q`, so
`x` belongs to `H`. Then

```text
{x,y,z}
```

is a minimal blocker: `P` is private for `y`, `Q` is private for `z`, and
`H` is private for `x`. These three distinct blockers accompany the fixed
blocker `{x,p}`, forcing `d(x)>=4`.

Thus every projection satisfying the stated two-row condition is impossible
in the degree-three branch.

## Seven-class application

For the nine endpoint projection representatives, endpoint `a` satisfies the
repaired lemma exactly in the following classes:

| Class | Row masks | Rows missing `a` | Endpoint intersection |
|---:|---|---|:---:|
| 2 | `10,11,13,18,21` | `R0,R3` | `{p}` |
| 3 | `10,13,13,18,21` | `R0,R3` | `{p}` |
| 4 | `10,13,15,18,21` | `R0,R3` | `{p}` |
| 6 | `10,13,18,21,27` | `R0,R2` | `{p}` |
| 7 | `10,13,18,21,29` | `R0,R2` | `{p}` |
| 8 | `10,13,18,21,31` | `R0,R2` | `{p}` |
| 9 | `10,13,19,21,22` | `R0,R4` | `{p}` |

Classes 1 and 5 fail the hypothesis and are precisely the two parallel
classes handled by the normal-form chain.

The companion script checks the nine row-mask representatives directly and
returns:

```text
excluded classes = 2,3,4,6,7,8,9
surviving classes = 1,5
mismatches = 0
```

## Evidence boundary

- `PROVED_CANDIDATE_REPAIRED_LEMMA`: the full-row intersection argument and
  the resulting three-blocker fan.
- `COMPUTED_EXACT_MAP`: direct mask verification of the seven applications;
  it is a transcription cross-check, not a proof dependency.
- No protected file, claim file, status file, commit, push, release, expert
  contact, or public action occurred.
