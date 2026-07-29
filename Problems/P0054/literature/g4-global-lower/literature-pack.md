# P0054 G4 frozen literature pack: global lower bounds for `sat(7)`

## Gate and evidence boundary

- `DEFINITION`: `RUN_MODE=GLOBAL_LOWER_BOUND_DISCOVERY` and
  `CURRENT_GATE=P0054_G4_GLOBAL_LOWER_BOUND_FOR_sat7`.
- `DEFINITION`: the primary candidate is `sat(7) >= 37`. It is not a fact
  imported from the literature and remains `CONJECTURED` until a complete
  proof and the required two-Referee audit both succeed.
- `LITERATURE`: the strongest directly checked published general theorem in
  this pack gives `sat(7) >= 10`, not merely 9; see Martin--Veldt Theorem 18
  and the exact specialization below.
- `UNKNOWN`: the global exact value of `sat(7)` and the existence of a public
  `sat(7) >= 36`, `sat(7) >= 37`, or stronger dedicated lower bound are not
  established by the recorded search.
- `UNKNOWN`: the negative search verdict is only
  `NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`. It is not a novelty,
  priority, openness, or global-absence claim.

This pack was assembled from two isolated read-only Scouts and an independent
main-Agent source check. The exact searches and access failures are in
`search-log.md`; theorem-to-obligation routing is in
`source-theorem-matrix.md`.

## Binding primary sources and version control

### Gerbner--Keszegh--Lemons--Palmer--Pálvölgyi--Patkós

`LITERATURE`: D. Gerbner, B. Keszegh, N. Lemons, C. Palmer,
D. Pálvölgyi, and B. Patkós, *Saturating Sperner Families*, Graphs and
Combinatorics 29 (2013), 1355--1364, DOI
[`10.1007/s00373-012-1195-6`](https://doi.org/10.1007/s00373-012-1195-6),
[arXiv:1105.4453](https://arxiv.org/abs/1105.4453).

- `LITERATURE`: Theorem 3(i) states the all-`n` relaxed bound
  `2^(k/2-1) <= wsat(n,k) <= sat(n,k)` for `k <= n`.
- `LITERATURE`: the same paper supplies the eventual stability result later
  used to define `sat(k)`.
- `LITERATURE`: the sharper pair-counting rearrangement quoted as
  Martin--Veldt Theorem 4 gives the historical integer baseline
  `sat(7) >= 9`; the displayed relaxed exponential bounds alone must not be
  rounded more strongly than their exact inequalities allow.

### Morrison--Noel--Scott

`LITERATURE`: N. Morrison, J. A. Noel, and A. Scott, *On Saturated
k-Sperner Systems*, Electronic Journal of Combinatorics 21(3) (2014),
P3.22, DOI [`10.37236/4136`](https://doi.org/10.37236/4136),
[VOR PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v21i3p22/pdf/),
[arXiv:1402.5646](https://arxiv.org/abs/1402.5646).

- `LITERATURE`: Definition 12 gives the canonical decomposition by iterative
  removal of inclusion-minimal members.
- `LITERATURE`: Lemma 13 gives a strict successor in the next antichain of a
  layered sequence; Lemma 14 says a layered sequence of pairwise-disjoint
  saturated antichains has saturated union.
- `LITERATURE`: Lemma 15 relates layering to small parts. Its printed wording
  says each layer has a homogeneous set; Martin--Veldt Lemma 12 is the binding
  later statement when one shared atom `H` is required.
- `LITERATURE`: Lemma 17 says that if a saturated `k`-Sperner family has a
  homogeneous set, every canonical layer is a saturated antichain.
- `LITERATURE`: Proposition 21 determines `sat(k)=2^(k-1)` only for `k<=5`;
  it gives no dedicated `k=7` lower bound.

### Martin--Veldt version of record

`LITERATURE`: R. R. Martin and N. Veldt, *Saturation of k-Chains in the
Boolean Lattice*, Electronic Journal of Combinatorics 32(1) (2025), P1.55,
DOI [`10.37236/12910`](https://doi.org/10.37236/12910),
[VOR PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i1p55/pdf/),
[arXiv:2402.14113v3](https://arxiv.org/abs/2402.14113v3).
The VOR, not arXiv v1/v2, is binding. The earlier 54-member claim was removed
and is not evidence.

- `DEFINITION`: `sat(n,k)` is the minimum size on an `n`-point ground set and
  `sat(k)` is its eventual stable value.
- `LITERATURE`: Lemma 6 states that `|X| > 2^|F|` guarantees a homogeneous
  atom, and that a saturated family cannot have two distinct homogeneous
  atoms. Thus `|F|<=55` and `n>2^55` are sufficient for this input, once `n`
  is also beyond the stabilization threshold.
- `LITERATURE`: Definitions 9--10 give the canonical decomposition and
  layered condition; Lemmas 12--13 respectively give the shared-atom
  layering criterion and saturation of canonical layers.
- `LITERATURE`: Proposition 14 gives, for a minimum-cardinality saturated
  family in the paper's lower-bound setup, endpoint layers `{empty}` and
  `{X}`, and the size constraints `|S|>=i` for small `S in A_i` and
  `|X\L|>=k-i-1` for large `L in A_i`.
- `LITERATURE`: Lemma 15 gives at least `k-2` small singletons and exactly one
  large member in `A_1`, with the dual statement for `A_(k-2)`. At `k=7`
  this yields `|A_1|>=6` and `|A_5|>=6` under all source hypotheses.
- `LITERATURE`: Lemma 17 is printed for `k>=7` and
  `2<=i<=floor((k-1)/2)`. It gives a general probabilistic internal-layer
  bound. It does not state the proposed exact `7,9,7` bounds.
- `LITERATURE`: Theorem 18 is printed for `k>=7` and gives
  `|F| >= 2^(k/2 + (1/2)log_2(k) - 1.66)` in the eventual lower-bound
  context. At `k=7`, the exponent is
  `3.2436774610288020537...` and the right side is
  `9.4720550193734449530...`; integrality therefore gives the published
  consequence `sat(7)>=10`.
- `LITERATURE`: Section 7 asks whether `sat(7)=56` or a smaller construction
  exists. The question is not a lower-bound or exact-value theorem.

## Source-text mismatch retained by this freeze

`LITERATURE`: the Martin--Veldt VOR, printed page 3, defines a homogeneous
atom using `|H|>=2`. The MNS source uses the same threshold. Some older local
P0053 source-pack and crosswalk files attribute `|H|>2` to that VOR.

`DEFINITION`: this G4 pack records that discrepancy as
`SOURCE_TEXT_MISMATCH_HOMOGENEOUS_THRESHOLD`. It does not rewrite historical
files. Offline proofs must use the actual VOR threshold or prove separately
why a stronger threshold is available. The mismatch is semantic source
fidelity, not a protected-file hash mismatch.

## 2025--2026 forward citations and adjacent work

- `LITERATURE`: Ji--Patkós--Yue, *Poset Saturation of Unions of Chains*,
  Order 43 (2026), article 17, DOI
  [`10.1007/s11083-026-09731-6`](https://doi.org/10.1007/s11083-026-09731-6),
  concerns induced/general poset-saturation parameters and is
  `RELATED_NOT_EQUIVALENT`.
- `LITERATURE`: PatternBoost reports a 108-member saturated 8-Sperner
  construction and is `RELATED_NOT_EQUIVALENT` to a 7-Sperner lower bound.
- `UNKNOWN`: Axenovich--Martin--Patkós, *Extremal Poset Theory*, Surveys in
  Combinatorics 2026, DOI
  [`10.1017/9781009766012.003`](https://doi.org/10.1017/9781009766012.003),
  was metadata-visible but full text was inaccessible. No claim about its
  treatment of `sat(7)` is frozen.

## Frozen inputs for offline discovery

The following are the only literature-level facts authorized for Phase 2--5:

1. `LITERATURE`: eventual stability of `sat(n,7)` and the existence of a
   sufficiently large `n` at which the stable value is attained.
2. `PROVED` in the existing repository: `sat(7)<=55`; this is used only to
   make `n>2^55` a uniform sufficient atom threshold.
3. `LITERATURE`: the canonical decomposition, saturated-layer result,
   endpoint normal form, size restrictions, and endpoint-layer lower bounds
   with their exact hypotheses.
4. `LITERATURE`: the currently checked published global consequence
   `sat(7)>=10`.
5. `CONJECTURED`: the proposed exact internal-layer bounds
   `|A_2|>=7`, `|A_3|>=9`, and `|A_4|>=7`, and their proposed sum to 37.

No offline Agent may infer priority, novelty, `sat(7)=55`, or a global lower
bound from a class-restricted P0054 certificate. No network access is allowed
after the hash manifest for this pack is written.

