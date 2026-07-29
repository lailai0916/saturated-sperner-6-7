# P0054 G4.13 scratch: P3+K2 normal-form audit v1

```text
STATUS: PROVED_CANDIDATE_NORMAL_FORM_PLUS_COMPUTED_EXACT_CROSSCHECK
SCOPE: P3+K2_FINAL_PARALLEL_CLASSES_MINIMAL_PAIR_LEGAL_NORMAL_FORMS
RESULT: FIRST_CLASS_32_AND_SECOND_CLASS_5_FROM_STRUCTURAL_PRIVATE_WITNESS_ANALYSIS
NETWORK: MATHEMATICS_OFFLINE
```

This note audits the two final `P3+K2` projection classes from first
principles. It closes the possible hidden case in which an outside point lies
on both duplicated rows, and it independently enumerates completions of every
cardinality rather than assuming the two- and three-point normal forms.

No global bound or protected claim changes here.

## Conventions

Rows are indexed `0,1,2,3,4`. The support of an outside point is the set of
rows containing it. A support is individually pair-legal when it has rank at
most three and does not cover all five rows together with the row support of
any endpoint. Two outside supports are pair-legal when their union is not all
five rows.

A minimal pair-legal completion satisfies:

- every row has size at least three;
- the five rows form a clutter;
- no endpoint-outside or outside-outside pair covers all rows;
- deleting any outside point breaks the row-size or clutter condition.

Repeated supports never occur in a minimal completion. If two outside points
have the same support, deleting either one leaves at least one copy on every
affected row. Each affected row starts with at least two endpoints, so its
size remains at least three. Every row-incomparability witness supplied by the
deleted point is also supplied by its twin. The deletion therefore preserves
both the row-size and clutter conditions, contradicting minimality. It is
enough to enumerate sets, rather than multisets, of supports.

The endpoint set of one row is already incomparable with that of another
unless an equality or inclusion is listed below. Adding outside points cannot
destroy an endpoint that already witnesses incomparability. Consequently the
listed equality/inclusions and the size-two rows are the only sources of
completion obligations.

## First parallel class

The endpoint rows are

```text
R0={p,u}
R1={p,u}
R2={a,q,u}
R3={p,v}
R4={a,q,v}.
```

The only endpoint equality or inclusion is `R0=R1`. Rows `R0`, `R1`, and
`R3` have size two.

### Exactly one left and one right witness

To make `R0` and `R1` incomparable, a completion needs a left witness `L`
in `R0` but not `R1`, and a right witness `M` in `R1` but not `R0`.

There cannot be two left witnesses in a minimal completion. Either one of
them is deletable while the other still supplies both the `R0` size deficit
and the left asymmetry, or one is the unique witness for `R3`, in which case
the other is deletable because the first still supplies the left obligation.
The same argument applies on the right. Thus there is exactly one `L` and
exactly one `M`.

An additional point can only be essential as the unique witness for the
size-two row `R3`. Such a point cannot lie on exactly one of `R0,R1`, since
it would be a second left or right witness. If it lies on both, its support
contains `{0,1,3}`, which forms a pair covering all rows with endpoint `a`
and also with endpoint `q`. Therefore every separate `R3` witness omits both
`R0` and `R1`. This rules out the hidden both-side-witness case.

### Allowed supports

For `L`, start with `{0}` and add at most two of `2,3,4`. The combinations
containing `{2,4}` form a pair with `p`, and those containing `{3,4}` form a
pair with `u`. Hence

```text
L in {{0},{0,2},{0,3},{0,2,3},{0,4}}
     = {1,5,9,13,17}.
```

By symmetry,

```text
M in {{1},{1,2},{1,3},{1,2,3},{1,4}}
     = {2,6,10,14,18}.
```

If neither side witness contains row `3`, the unique separate witness omits
rows `0,1` and contains row `3`. It cannot also contain row `4`, because
`{3,4}` pairs with endpoint `u`. Therefore

```text
T in {{3},{2,3}} = {8,12}.
```

If `L` or `M` contains row `3`, the completion is the pair `[L,M]`; the
outside-pair rule leaves 14 possibilities. If neither contains row `3`, the
completion is `[L,M,T]`; all `3*3*2=18` possibilities are pair-legal. The
complete structural list therefore has `14+18=32` members.

Every listed point is essential: deleting `L` or `M` reopens a size deficit
and destroys one direction of the `R0/R1` incomparability; when present,
deleting `T` reopens the `R3` size deficit. Thus the list contains only
minimal completions.

## Second parallel class

The endpoint rows are

```text
R0={p,u}
R1={a,q,u}
R2={p,v}
R3={a,q,v}
R4={p,u,v}.
```

The only endpoint inclusions are `R0` contained in `R4` and `R2` contained
in `R4`; precisely `R0` and `R2` have size two. Each needs an outside
witness that lies on the smaller row and omits `R4`. These witnesses also
fill the two size deficits.

A single combined witness contains rows `0,2` and omits row `4`. Rank at
most three leaves `{0,2}`, `{0,1,2}`, and `{0,2,3}`. The latter two form
endpoint pairs with `v` and `u`, respectively. Hence the unique combined
completion is

```text
[5] = [{0,2}].
```

Otherwise the obligations use separate witnesses. The `R0` witness contains
row `0` and omits rows `2,4`; endpoint-pair legality leaves only `{0}` and
`{0,3}`. The `R2` witness contains row `2` and omits rows `0,4`; legality
leaves only `{2}` and `{1,2}`. Their four products are pair-legal:

```text
[1,4], [1,6], [4,9], [6,9].
```

Any additional point would be deletable because the two size and private-row
obligations are already met. Thus these five completions are exhaustive and
minimal.

## Independent exhaustive replay

`p0054_g413_p3k2_normal_form_audit_v1.js` derives every individually legal
support, then scans every subset of those supports. The repeated-support
argument above makes this exhaustive over arbitrary finite outside point
sets. The script imposes no completion-cardinality bound.

```text
first class:
  allowed supports = 16
  subsets scanned = 2^16 = 65536
  minimal completions = 32 = 14 of size 2 + 18 of size 3
  hidden both-side witnesses = 0

second class:
  allowed supports = 14
  subsets scanned = 2^14 = 16384
  minimal completions = 5 = 1 of size 1 + 4 of size 2

structural-list mismatches = 0
expected-list mismatches = 0
```

The exhaustive replay independently verifies the 32- and 5-member lists and
also verifies that no larger minimal completion was omitted.

## Evidence boundary

- `PROVED_CANDIDATE_NORMAL_FORM`: the private-witness arguments above derive
  all 32 and 5 normal forms.
- `COMPUTED_EXACT_CROSSCHECK`: exhaustive subset enumeration agrees exactly
  with both structural lists and the earlier checker lists.
- This does not promote the G4.13 candidate chain to a protected theorem and
  does not change the current global interval.
- No protected file, claim file, status file, commit, push, release, expert
  contact, or public action occurred.
