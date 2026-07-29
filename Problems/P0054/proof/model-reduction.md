# P0054 model reduction

## Claim

Fix a seven-element core `C`, a disjoint block `H` with `|H| > 2`, and seven
ordered families whose members all have the form `A` or `A ∪ H` for `A ⊆ C`.
There is no such system of total size at most 55 satisfying pairwise
disjointness, saturated-antichain layers, and the layered condition.

Together with the Martin--Veldt 56-member construction, this says that 56 is
the exact minimum **inside this fixed seven-core template class**.  It does not
prove `sat(7)=56` among arbitrary saturated 7-Sperner systems.

## 1. Three signatures are complete

For an arbitrary subset `S ⊆ C ∪ H`, record

1. its core mask `S ∩ C`; and
2. whether `S ∩ H` is empty, a nonempty proper subset, or all of `H`.

These are the `EMPTY`, `PARTIAL`, and `FULL` states.  Every state is realizable
because `|H| > 2`.  Inclusion between `S` and any template `A` or `A ∪ H`
depends only on this signature.  The four cases are enumerated in
`signature_strictly_comparable` and are exhaustively compared with real sets in
`test_symbolic_comparability_matches_explicit_sets`.

Consequently, a template family is a saturated antichain in the full powerset
if and only if:

- no two selected templates are comparable; and
- every one of the `3 * 2^7` signatures is either an exact selected template or
  is strictly comparable with a selected template.

The same statement holds for any finite core size.

## 2. Primary Boolean variables

For layer `i`, atom-use bit `b`, and core mask `m`, the primary variable is

```text
x(i,b,m) = 1 + i * 2^(r+1) + b * 2^r + m,
```

where `0 ≤ i < 7`, `b ∈ {0,1}`, and `0 ≤ m < 2^r`.  It is true exactly
when the corresponding template occurs in layer `i`.

The CNF contains:

- one binary exclusion for every comparable pair in a layer;
- one positive coverage clause for every layer and signature;
- pairwise exclusions placing each template in at most one layer;
- the implication from each selected upper-layer template to the disjunction
  of its strict predecessors in the preceding layer; and
- a self-contained Sinz-style sequential-counter CNF for at most 55 true
  primary variables.

Thus every mathematical candidate of size at most 55 extends to a satisfying
assignment of the CNF.  Conversely, the primary part of any satisfying
assignment decodes to a candidate and is accepted by both semantic verifiers.
Only the forward implication is needed for the lower bound.

## 3. Independent controls

- The symbolic signature verifier and a second verifier that expands `H` to
  three actual points both accept the published 56-member construction.
- Fixing that construction in the independently generated CNF at bound 56 is
  satisfiable.
- Symbolic inclusion and comparability agree exhaustively with expanded sets
  for every core through size three.
- Z3 and the CNF solver agree on the tiny-core control instance.

These controls specifically test against an over-constrained encoding that
would incorrectly exclude the known construction.

## 4. Certificate-backed lower bound

For `r=7` and target 55, the self-contained deterministic CNF has 100,297
variables (1,792 primary and 98,505 sequential-counter auxiliaries) and 252,427
clauses.  Kissat 4.0.4 returned UNSAT and wrote a 253,731,315-byte binary DRAT
proof.  DRAT-trim at commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985` checked the proof and returned
`s VERIFIED`.

Artifact hashes and the checker transcript are stored in
`experiments/certificates/verification-manifest.json`.

## 5. Remaining trust and novelty boundary

The clausal proof is independently machine checked, but this reduction is still
a human-readable proof rather than a Lean formalization.  A specialist must
review the definition boundary, and a final literature audit must precede any
novelty claim.  Larger cores and non-template constructions remain outside the
theorem.
