# A 55-member saturated 7-Sperner construction

## Theorem

Let `C={1,...,8}` and let `H` be disjoint from `C`, with `|H|>2`.  If a digit
string denotes the corresponding subset of `C` and a trailing `H` denotes union
with the whole block `H`, define the following seven layers:

```text
A0 = { empty }

A1 = { 1, 2, 3, 6, 7, 458H }

A2 = { 24, 15, 35, 26, 47, 67, 18, 38,
       1346H, 1237H, 4568H, 2578H }

A3 = { 124, 234, 145, 345, 156, 356, 267, 178, 378,
       12357H, 13467H, 12358H, 12368H, 13468H,
       24568H, 24578H, 45678H }

A4 = { 2345, 1247, 3568, 1678,
       123567H, 134567H, 123468H, 124568H,
       123578H, 134578H, 234678H, 245678H }

A5 = { 23457, 1234568H, 1234678H, 1235678H,
       1245678H, 1345678H }

A6 = { 12345678H }
```

Then `F=A0 union ... union A6` is a saturated 7-Sperner family of size 55.
It has layer sizes `(1,6,12,17,12,6,1)`, with 28 members avoiding `H` and 27
members containing `H`.

Consequently,

```text
sat(n,7) <= 55 for every n >= 11,
sat(7) <= 55.
```

Here `sat(7)` is the stable limiting saturation number used by Martin--Veldt.

## Proof certificate and reduction

For a subset `S` of `C union H`, comparability with a template depends only on
`S intersect C` and whether `S intersect H` is empty, nonempty proper, or all of
`H`.  These `3*2^8=768` signatures are exhaustive for every `|H|>2`.

The signature verifier checks for each layer that:

1. its selected templates form an antichain;
2. every unselected signature is strictly comparable with a selected member;
3. the layers are pairwise disjoint; and
4. every member in `Ai`, for `i>0`, strictly contains a member of `A(i-1)`.

It accepts the displayed family after 5,376 layer-signature checks.  Thus every
`Ai` is a saturated antichain and the sequence is layered.  Martin--Veldt Lemma
11 then proves that their union is saturated 7-Sperner.

Three additional checks do not trust that reasoning path:

- expansion with a three-point `H` checks all layer conditions directly on the
  11-point ground set;
- an integer-bitmask dynamic-programming verifier checks that the union has no
  8-chain and exhausts all 1,993 sets outside the family; and
- a separately implemented `frozenset` DAG verifier repeats the same direct
  union-level test.

All four checks accept the same semantic family hash
`8277267a7a9cbc6040432a9d6ffc3f16c540a6013b78bedbd85e6b1e27adde0f`.

The SAT solver was only a discovery mechanism.  Correctness of the displayed
family does not depend on trusting the solver, its CNF, or its model extraction.

## Iterated consequence

The composition lemma used by Morrison--Noel--Scott and Martin--Veldt multiplies
the small-part sizes and the large-part sizes separately.  Iterating the new
base family `j>=1` times, and using the usual remainder construction for
`0<=s<=4`, gives

```text
sat(5*j + 2 + s) <= 2^s * (28^j + 27^j).
```

This strictly improves the previous discrete bound `2^(s+1)*28^j` for every
`j>=1`, although the leading asymptotic exponent is unchanged because the
larger part still has size 28.

## Evidence boundary

The construction proves an upper bound, not the exact value of `sat(7)`.  The
bounded literature audit through 2026-07-21 found no valid 55-member result,
but public novelty remains `UNKNOWN` until specialist review and a final
bibliographic audit.

The withdrawn arXiv v1/v2 construction in `arXiv:2402.14113` claimed size 54.
The current verifiers reject it: its third layer is not saturated, with the
core set `{2,3,6}` as a witness.  The final published paper explicitly records
that the earlier lower value was erroneous.

