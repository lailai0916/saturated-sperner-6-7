# P0054 G4.13 scratch: P3+K2 residue structural closure v1

```text
STATUS: PROVED_CANDIDATE_STRUCTURAL_CLOSURE_PLUS_COMPUTED_EXACT_CROSSCHECK
SCOPE: P3+K2_TEN_PATTERN_RESIDUE
RESULT: NINE_PATTERNS_EXCLUDED_BY_ONE_TWIN_ENDPOINT_AMPLIFIER; FINAL_PATTERN_EXCLUDED_BY_EXTENSION_CLOSED_KERNEL
NETWORK: MATHEMATICS_OFFLINE
```

This note compresses the ten-pattern residue in
`p0054_g413_p3k2_parallel_residue_v2.md`.

It does not change the theorem value or any protected artifact. The reduction
to the ten patterns keeps its existing evidence boundary. Only the final
obstruction is simplified here.

## Twin endpoint amplifier

Let two distinct points `a,q` have the same row support. Suppose two distinct
minimal blockers `B1,B2` contain `a`, omit `q`, and share a point `t`.
Replacing `a` by `q` preserves both row coverage and every private-row
witness. Therefore

```text
B1, B2, (B1\{a}) union {q}, (B2\{a}) union {q}
```

are four distinct minimal blockers containing `t`. Hence `d(t)>=4`.

This elementary symmetry is the only degree argument needed for nine of the
ten residual patterns.

## Point-in-blocker lemma

Every point of a finite clutter lies in a minimal blocker. Indeed, let `t`
belong to a row `F`. The set

```text
{t} union (V\F)
```

hits every row. A row missing `t` cannot be contained in `F\{t}`, since that
would violate the clutter property. After minimizing the displayed
transversal, `t` remains necessary because `F` is private for it.

Consequently, restoring a deleted point creates at least one new blocker
containing that point.

## First parallel class

The fixed supports are:

```text
S_a=S_q={2,4}
S_p={0,1,3}
S_u={0,1,2}
S_v={3,4}
```

The row swap `R0 <-> R1` pairs the eight residual patterns. They fall into
two structural families.

### Bridge-point family

Up to the row swap, the six patterns are:

```text
[1,10], [1,14], [5,10]
```

Write their outside points as `x,y`. Then:

```text
S_x in {{0},{0,2}}
S_y in {{1,3},{1,2,3}}
```

The two blockers

```text
{a,u,y}, {a,x,y}
```

are minimal. For the first, private rows for `a,u,y` are respectively
`R4,R0,R3`. For the second, private rows for `a,x,y` are respectively
`R4,R0,R1` or `R3`.

Both blockers contain `y`. The twin endpoint amplifier replaces `a` by `q`
and gives four blockers containing `y`. Thus `d(y)>=4`.

The row swap adds:

```text
[2,9], [2,13], [6,9]
```

so this family excludes six residual patterns.

### Split-bridge family

Up to the row swap, the remaining pattern is:

```text
[1,6,8]
```

Write the outside supports as:

```text
S_x={0}, S_y={1,2}, S_z={3}
```

The two blockers

```text
{a,u,z}, {a,x,y,z}
```

are minimal. Their private rows are respectively:

```text
{a,u,z}:   R4,R0,R3
{a,x,y,z}: R4,R0,R1,R3
```

Both contain `z`. The twin endpoint amplifier gives four blockers containing
`z`, so `d(z)>=4`.

The row swap gives `[2,5,8]`. This excludes the final two residual patterns in
the first parallel class.

## Second parallel class

The fixed supports are:

```text
S_a=S_q={1,3}
S_p={0,2,4}
S_u={0,1,4}
S_v={2,3,4}
```

### Single-point pattern

For `[5]`, the outside point `x` has support `{0,2}`. The two minimal blockers

```text
{a,u,x}, {a,v,x}
```

share `x`. Replacing `a` by `q` gives two more. Hence `d(x)>=4`.

### Seven-blocker kernel

For `[1,4]`, write the two outside points as `z,w` with supports `{0}` and
`{2}`. The kernel has exactly seven blockers:

```text
{a,p}, {p,q}, {u,v},
{a,u,w}, {q,u,w},
{a,v,z}, {q,v,z}
```

The points `a,q,u,v` are saturated at degree three. The unsaturated points
`p,w,z` cover only rows `{0,2,4}`.

Let a restored point `t` have nonempty support `S` of size at most three. By
the point-in-blocker lemma, `t` belongs to a new minimal blocker.

- If `S` misses row `1` or row `3`, every new blocker containing `t` needs
  one of `a,q,u,v`, so it increases a saturated degree.
- If `{1,3}` is contained in `S` and `0` is in `S`, then `{v,t}` is a new
  pair blocker.
- If `{1,3}` is contained in `S` and `2` is in `S`, then `{u,t}` is a new
  pair blocker.
- Otherwise `{1,3}` is contained in `S` while `0,2` are absent. Then
  `{t,u,w}` is a minimal blocker with private rows `R3,R0,R2`.

Every possible restored support raises the degree of a saturated endpoint.
The seven-blocker kernel is therefore extension-closed inside the degree-three
branch.

## Cross-check

An independent direct powerset enumerator recomputed all minimal blockers for
the ten patterns.

```text
first class:
[1,6,8]  high degrees y=4, z=4
[1,10]   high degree  y=4
[1,14]   high degree  y=6
[2,5,8]  high degrees y=4, z=4
[2,9]    high degree  y=4
[2,13]   high degree  y=6
[5,10]   high degrees x=4, y=5
[6,9]    high degrees x=4, y=5

second class:
[5]      high degree  x=4
[1,4]    degree-legal seven-blocker kernel, excluded only after restoration
```

The replay agrees exactly with `p0054_g413_p3k2_parallel_residue_v2.md`.

## Boundary

- `PROVED_CANDIDATE`: the twin endpoint amplifier, both support families, and
  the extension-closed kernel argument.
- `COMPUTED_EXACT_CROSSCHECK`: the independent powerset replay.
- No protected G4.12 file, claim file, status file, commit, push, release,
  expert contact, or public action occurred.
