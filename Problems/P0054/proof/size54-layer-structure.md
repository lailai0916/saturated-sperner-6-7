# Structural layer bounds for the eight-core size-54 problem

## Scope

Let `C` have eight elements, let `H` be a disjoint block with `|H|>2`, and
let `A_0,...,A_6` satisfy the complete common-block layered template problem
in `statement.md`.  This note proves structural restrictions inside that
class.  It does not prove a global lower bound for `sat(7)`.

Write the template rank as

```text
rho(A) = |A|,
rho(A union H) = |A| + 1.
```

Thus the template poset is a nine-rank Boolean lattice when `|C|=8`, even
though the actual block `H` contains more than one point.

## Proposition 1 — every member has a successor

For every `i<6` and every `X in A_i`, there is `Y in A_(i+1)` with `X subset Y`.

### Proof

The layers are disjoint, so `X` is external to the saturated antichain
`A_(i+1)`.  Hence some `Y in A_(i+1)` is strictly comparable with `X`.
Suppose for contradiction that `Y subset X`.  The stated predecessor condition
for `Y` supplies `X' in A_i` with `X' subset Y`.  Then

```text
X' subset Y subset X,
```

contradicting that `A_i` is an antichain.  Therefore `X subset Y`.

This also fills the logical step needed by the complement-and-layer-reversal
duality in `size54-oriented-reduction.md`.

## Corollary 2 — full chains and four-rank windows

Every member of `A_i` lies on a strict chain containing one member of every
layer.  The predecessor hypotheses extend it down to `A_0`, and Proposition 1
extends it up to `A_6`.  Six strict inclusions fit inside template ranks
`0,...,9`.  Therefore

```text
i <= rho(X) <= i+3                         (2)
```

for every `X in A_i`.  The seven windows are

```text
[0,3], [1,4], [2,5], [3,6], [4,7], [5,8], [6,9].
```

Complementation sends rank `q` to rank `9-q` and layer `i` to layer `6-i`, so
the windows are exchanged in reverse order.

## Proposition 3 — exact independent layer minima

Among saturated template antichains contained in the respective rank windows,
the exact minimum sizes are

```text
(1, 6, 12, 14, 12, 6, 1).                 (3)
```

### Exact finite reduction

For a fixed layer, retain only templates in its window.  The CNF contains:

1. a binary exclusion for every comparable selected pair;
2. for every `R subset C`, the exact oriented saturation clause

   ```text
   some selected small S satisfies S subset R,
   or some selected large L union H satisfies R subset L;
   ```

3. a self-contained sequential counter for the proposed upper bound.

The oriented clause is necessary and sufficient by Proposition 1 of
`size54-oriented-reduction.md`.  Consequently the CNF is satisfiable exactly
when such a rank-confined saturated antichain exists.

Kissat 4.0.4 proved UNSAT at bounds `0,5,11,13` for layers `0,1,2,3`.
DRAT-trim at commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`
independently returned `s VERIFIED` on all four proof files.  This proves the
lower bounds `1,6,12,14`.  Complement duality proves `12,6,1` for the remaining
layers.

The bounds are sharp.  Layers `0,1,2,4,5,6` of the verified 55-member family
have sizes `1,6,12,12,6,1`.  A separately checked middle-layer witness has
seven rank-3 small templates with masks

```text
14, 52, 88, 98, 146, 168, 196
```

and seven rank-6 large templates with masks

```text
59, 87, 109, 157, 167, 203, 241.
```

It is an antichain and satisfies all 256 oriented coverage clauses.  Hence the
middle minimum is exactly 14.  It is also complement-invariant: the seven mask
pairs are `14/241`, `52/203`, `88/167`, `98/157`, `146/109`, `168/87`, and
`196/59`, with small and large roles exchanged.

The certificate manifest is
`experiments/size54-g3-layer-bounds/verification-manifest.json`, with semantic
SHA-256
`61d4aad46a3257c3845ccccd8c18e75d49d24eccdf2ab767d897d1f9c64e2b6d`.

## Corollary 4 — only two slack units at target 54

The values in (3) sum to 52.  Therefore any full system of total size at most
54 has at most two members beyond the independent layer minima.  In
particular, every layer has the safe upper bound

```text
(3, 8, 14, 16, 14, 8, 3).                 (4)
```

Distributing exactly two indistinguishable slack units among seven layers
gives 28 componentwise upper-bound profiles.  Every actual slack vector of sum
zero, one, or two is bounded by at least one of them.

## Proposition 5 — one sharp middle layer cannot extend

Fix the displayed complement-invariant 14-member middle-layer witness.  Add the complete seven-layer
antichain, oriented coverage, disjointness, predecessor, successor, total-size,
small-template symmetry, and bounds (4) to the CNF.  Kissat returned UNSAT in
10.54 seconds, producing a 42,951,282-byte DRAT proof.  DRAT-trim independently
returned `s VERIFIED`.  Thus this particular sharp middle layer cannot occur
in a size-at-most-54 full system.

This proposition does not classify all 14-member middle layers and therefore
does not exclude every size-54 system.

## Remaining boundary

The complete reduced system has 1,934 primary variables, 152,394 auxiliary
variables, and 338,735 clauses.  Kissat reached its 1,800-second limit without
SAT or UNSAT.  Each of the 28 slack profiles likewise reached 60 seconds
without a conclusion.  These timeouts are `COMPUTED` records with no
mathematical consequence.

The exact eight-core template-class minimum remains either 54 or 55.  The
global exact value of `sat(7)` remains unknown.
