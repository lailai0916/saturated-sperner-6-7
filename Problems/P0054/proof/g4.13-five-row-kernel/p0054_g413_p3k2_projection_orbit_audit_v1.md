# P0054 G4.13 scratch: P3+K2 projection orbit audit v1

```text
STATUS: PROVED_CANDIDATE_CLASSIFICATION_PLUS_COMPUTED_EXACT_ORBIT_CROSSCHECK
SCOPE: P3+K2_FIVE_ROW_ENDPOINT_PROJECTIONS
RESULT: EXACTLY_NINE_ORBITS_FROM_FIVE_D_COUPLINGS_AND_FOUR_I_COUPLINGS
NETWORK: MATHEMATICS_OFFLINE
```

This note audits the endpoint-projection classification in
`p0054_g413_p3k2_pure_projection_v2.md`.

It does not change the theorem value or any protected artifact. The hand
classification and the independent orbit enumeration use only the fixed pair
graph `P3+K2` and the five-row rank bound.

## Support types

Let `R={0,1,2,3,4}`. For an endpoint `x`, write `S_x` for its row support and
`A_x=R\S_x` for its avoidance set.

For every fixed pair `{x,y}`:

```text
S_x union S_y=R
```

and both support sizes are at most three. Neither support can have size one,
because its partner would then need size at least four. Hence every fixed pair
has exactly one of two forms:

- Type `D`: support sizes two and three, with empty intersection.
- Type `I`: both support sizes are three, with one common row.

For endpoints `x,y` that are not adjacent in `P3+K2`, their pair is not a
transversal. Equivalently:

```text
A_x intersection A_y is nonempty.
```

## Avoidance intersection lemma

Consider two fixed edges on disjoint endpoint sets. Every one of the four
cross-intersections between their avoidance sets is nonempty.

This gives three cases.

- `D-D`: two `2+3` partitions have a positive `2 by 2` intersection matrix.
  Its entries are forced to be `2,1,1,1`, up to exchanging blocks.
- `I-D`: let `w` be the common support row of the type `I` edge. Its two
  avoidance sets partition `R\{w}` into two pairs. The row `w` lies in the
  three-block of the type `D` avoidance partition. After deleting `w`, the
  two `2+2` partitions meet once in every cell.
- `I-I`: the two common rows are equal. Otherwise the four disjoint nonempty
  avoidance intersections would lie in only three rows. After deleting the
  common row, the two `2+2` partitions again meet once in every cell.

These intersection patterns are unique up to row permutation and endpoint
swaps within the two fixed edges.

## Five path types

The path edges are `{a,p}` and `{p,q}`.

If `|S_p|=2`, both edges have type `D`, and:

```text
S_a=S_q=R\S_p.
```

This is path type 3.

If `|S_p|=3`, each of `S_a,S_q` is either `R\S_p` or that two-set plus one
row of `S_p`. Up to exchanging `a,q`, this gives four more types:

1. both edges are `D`;
2. exactly one edge is `I`;
4. both edges are `I` with the same common row;
5. both edges are `I` with different common rows.

Together with the `|S_p|=2` case, these are exactly the five path types.

## Coupling a type D independent edge

Let `{u,v}` have type `D`.

- Path types 1 and 3 reduce directly to the unique `D-D` intersection
  matrix.
- In path type 2, the `D-D` matrix fixes the partition. The common row of the
  type `I` path edge must lie in the three-block. Remaining choices are row
  symmetric.
- In path type 4, delete the shared common row. The two remaining `2+2`
  partitions must be orthogonal, which is unique up to symmetry.

For path type 5, write:

```text
S_p={r,s,t}
S_a={b,c,r}
S_q={b,c,s}
```

The three-block of the independent type `D` avoidance partition must contain
both `r` and `s`. Orthogonality with the two path partitions forces its third
row to be one of `b,c`, not `t`. Exchanging `b,c` identifies the two choices.

Thus all five path types admit exactly one type `D` coupling.

## Coupling a type I independent edge

Let `{u,v}` have type `I`, with common row `w`.

- Every type `I` path edge must have the same common row `w`.
- For every type `D` path edge, `w` must lie in the three-block of its
  avoidance partition.

Path types 1, 2, 3, and 4 each satisfy these conditions in one orbit. Path
type 5 has two different type `I` common rows, so it is impossible.

Therefore the coupling count is:

```text
5 type-D couplings + 4 type-I couplings = 9 endpoint projections.
```

## Representatives

The support strings list row indices. The row masks use endpoint-bit order
`a,p,q,u,v`.

| Class | Path type | Edge type | `S_a,S_p,S_q,S_u,S_v` | Row masks | Orbit size |
|---:|---:|:---:|:---:|:---:|---:|
| 1 | 1 | `D` | `24,013,24,012,34` | `10,10,13,18,21` | 120 |
| 2 | 2 | `D` | `124,013,24,012,34` | `10,11,13,18,21` | 480 |
| 3 | 3 | `D` | `124,03,124,012,34` | `10,13,13,18,21` | 120 |
| 4 | 4 | `D` | `124,023,124,012,34` | `10,13,15,18,21` | 240 |
| 5 | 1 | `I` | `13,024,13,014,234` | `10,13,18,21,26` | 120 |
| 6 | 2 | `I` | `134,024,13,014,234` | `10,13,18,21,27` | 240 |
| 7 | 3 | `I` | `134,02,134,014,234` | `10,13,18,21,29` | 120 |
| 8 | 4 | `I` | `134,024,134,014,234` | `10,13,18,21,31` | 120 |
| 9 | 5 | `D` | `123,024,134,01,234` | `10,13,19,21,22` | 240 |

## Independent orbit cross-check

An independent enumerator used all 20 two- or three-subsets of `R` as support
candidates. It retained ordered tuples `(S_a,S_p,S_q,S_u,S_v)` exactly when:

- the three graph edges have support union `R`;
- every graph nonedge has support union different from `R`.

The result is:

```text
labeled_legal_support_tuples=1800
quotient_group=S_5 times Aut(P3+K2)
Aut(P3+K2)=<a<->q, u<->v>
orbit_count=9
orbit_sizes=120,120,120,120,120,240,240,240,480
hand_representatives_missing=0
enumerated_orbits_missing_from_hand_list=0
```

The orbit sizes sum to 1800. Each hand representative lies in a distinct
orbit, and the hand list covers every enumerated orbit.

## Count provenance

The older note records `8500 endpoint assignments` from a historical checker.
That number is not the count of completed labeled support tuples under the
explicit conditions above. The current temporary artifacts do not preserve a
stage definition that makes the two counts directly comparable.

Accordingly, `8500` remains historical checker telemetry. It is not used in
this classification or presented as a second count of the same object.

## Boundary

- `PROVED_CANDIDATE`: the `D/I` classification, five path types, avoidance
  intersection lemma, and `5+4` coupling argument.
- `COMPUTED_EXACT_ORBIT_CROSSCHECK`: the 1800 labeled tuples and nine orbit
  comparison.
- No protected G4.12 file, claim file, status file, commit, push, release,
  expert contact, or public action occurred.

