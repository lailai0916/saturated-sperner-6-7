# P0054 G4.13 scratch: P3+K2 endpoint structural classifier v1

```text
STATUS: PROVED_CANDIDATE_STRUCTURAL_CLASSIFIER_PLUS_COMPUTED_EXACT_MATCH
SCOPE: P3+K2_PARALLEL_NORMAL_FORM_ENDPOINT_DEGREE_PRUNING
RESULT: FIRST_CLASS_24_EXCLUSIONS_AND_SECOND_CLASS_3_EXCLUSIONS_FROM_THREE_PRESSURE_MECHANISMS
NETWORK: MATHEMATICS_OFFLINE
```

This note replaces the per-pattern endpoint classifier in
`p0054_g413_p3k2_endpoint_classifier_audit_v1.md` with structural conditions.

It does not change the theorem value or any protected artifact. The existing
JSON witness audit remains an exact cross-check, not a primary proof
dependency.

## Degree budget

In the `P3+K2` pair graph, the fixed blockers are:

```text
{a,p}, {p,q}, {u,v}.
```

Thus `p` already lies in two blockers. Any two further blockers containing
`p` force `d(p)>=4`. Each of `a,q,u,v` already lies in one blocker. Three
further blockers containing any one of them force degree at least four.

## First parallel class

The fixed supports are:

```text
S_a=S_q={2,4}
S_p={0,1,3}
S_u={0,1,2}
S_v={3,4}
```

Write the two asymmetric side witnesses as `X0,X1`, where:

```text
S_X0 in {{0},{0,2},{0,3},{0,2,3},{0,4}}
S_X1 in {{1},{1,2},{1,3},{1,2,3},{1,4}}.
```

If neither side witness contains row `3`, a separate witness `T` has support
`{3}` or `{2,3}`.

### Central special-witness pressure

Every outside witness `X` containing row `2` creates a minimal blocker:

```text
{p,v,X}.
```

The private rows are row `2` for `X`, row `4` for `v`, and row `0` or `1`
for `p`.

Every side witness `Y` containing row `4` creates another minimal blocker:

```text
{p,u,Y}.
```

Its private rows are row `4` for `Y`, row `2` for `u`, and row `3` for `p`.

Call these row-`2` and row-`4` points special witnesses. Two distinct special
witnesses give two further blockers containing `p`, so they violate the
degree budget.

### Three-point case

Here `X0,X1` omit row `3`, and `T` supplies row `3`.

If there are at least two special witnesses, central pressure gives
`d(p)>=4`.

Suppose there is at most one special witness. The only possibility not
excluded by endpoint pressure is:

```text
T has support {3};
neither side witness uses row 4;
exactly one side witness uses row 2.
```

Indeed, if the unique special witness is not a side witness using row `2`, or
if no special witness exists, the following are three distinct minimal
blockers containing `a`:

```text
{a,v,X0,X1}
{a,u,T}
{a,X0,X1,T}
```

For the first blocker, private rows are `2,3,0,1`. For the second they are
`4,0/1,3`. For the third, `X0,X1,T` have private rows `0,1,3`, while `a` has
private row `2` or `4`.

Together with `{a,p}`, these blockers force `d(a)>=4`.

The complete blocker replay confirms that the endpoint-degree-legal patterns
are exactly:

```text
[1,6,8], [2,5,8].
```

### Two-point case

At least one of `X0,X1` contains row `3`.

If both contain row `3`, the following three blockers contain `a`:

```text
{a,u,X0}
{a,u,X1}
{a,X0,X1}
```

Their private rows follow directly from rows `0,1,3,4`. Hence `d(a)>=4`.

Now suppose exactly one side witness, denoted `X3`, contains row `3`.

- If both side witnesses use row `2`, central pressure forces `d(p)>=4`.
- If the other side witness `X4` uses row `4`, the three blockers
  `{a,u,X3}`, `{q,u,X3}`, and `{p,u,X4}` accompany `{u,v}`, so `d(u)>=4`.
- In every other pair-legal case, all endpoint degrees are at most three.

The complete blocker replay confirms that the endpoint-degree-legal patterns
are exactly:

```text
[1,10], [1,14], [2,9], [2,13], [5,10], [6,9].
```

The first parallel class therefore has exactly eight endpoint-degree-legal
minimal completions. The other 24 are excluded by the three pressure
mechanisms above.

## Second parallel class

The fixed supports are:

```text
S_a=S_q={1,3}
S_p={0,2,4}
S_u={0,1,4}
S_v={2,3,4}
```

Separate private witnesses have supports:

```text
S_X0 in {{0},{0,3}}
S_X2 in {{2},{1,2}}.
```

The combined private witness has support `{0,2}`.

If `X2` uses row `1` while `X0` omits row `3`, then:

```text
{u,v}, {a,v,X0}, {q,v,X0}, {p,v,X2}
```

force `d(v)>=4`.

If `X0` uses row `3` while `X2` omits row `1`, the symmetric blockers:

```text
{u,v}, {a,u,X2}, {q,u,X2}, {p,u,X0}
```

force `d(u)>=4`.

If both mixed rows occur, the two new blockers:

```text
{p,v,X2}, {p,u,X0}
```

accompany `{a,p}` and `{p,q}`, so `d(p)>=4`.

Therefore `[1,6]`, `[4,9]`, and `[6,9]` are excluded. The endpoint-degree
legal patterns are exactly `[1,4]` and `[5]`.

## Exact match

The structural classifier selects:

```text
first class:  8 accepted, 24 rejected
second class: 2 accepted, 3 rejected
```

Up to the row swap `R0 <-> R1`, the accepted endpoint degree vectors in the
first class are:

```text
pattern    a,p,q,u,v
[1,6,8]   3,3,3,3,3
[1,10]    3,2,3,3,1
[1,14]    3,3,3,3,3
[5,10]    3,3,3,3,3
```

The accepted second-class vectors are:

```text
pattern  a,p,q,u,v
[1,4]   3,2,3,3,3
[5]     3,2,3,3,3
```

Its accepted support lists match the existing exhaustive classifier
byte-for-byte at the support-set level. The private-row witnesses above also
match the 27 cases in
`p0054_g413_p3k2_endpoint_classifier_audit_v1.json`.

## Boundary

- `PROVED_CANDIDATE`: the degree budget, central special-witness pressure,
  path-endpoint fans, independent-edge fans, and their coverage of every
  normal-form pattern outside the listed 8+2 survivors.
- `COMPUTED_EXACT_MATCH`: the survivor degree vectors, comparison with the
  32+5 normal-form support lists, and the 27-case witness sidecar.
- No protected G4.12 file, claim file, status file, commit, push, release,
  expert contact, or public action occurred.
