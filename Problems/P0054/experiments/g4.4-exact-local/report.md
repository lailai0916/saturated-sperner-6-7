# P0054 G4.4 exact-local incidence search

## Scope and verdict

`DEFINITION`: the requested objects are finite mutual-blocker clutter pairs
`(mathcal S, mathcal C)` on an arbitrary finite ground set `U`, with

```text
mathcal S = B(mathcal C),  mathcal C = B(mathcal S),
min_{S in mathcal S}|S| >= 2,  min_{C in mathcal C}|C| >= 4.
```

Write `a=|mathcal S|` and `b=|mathcal C|`.

`COMPUTED`: a fresh deterministic incidence-pattern enumeration completed
every admissible split with `a+b` equal to 9, 10, or 11. All 15 splits have
`complete_exhaustion=true` and status `UNSAT_COMPUTED` in `results.json`.
This includes the six frozen unresolved splits

```text
(5,4), (6,4), (5,5), (7,4), (6,5), (5,6).
```

It also explicitly includes the boundary splits with `b=2`, `b=3`, or
`a=4`, rather than importing their previously proved exclusions.

`COMPUTED`: no SAT case occurred, so there is no `U/S/C` witness to save.
The source is prepared to save complete `U`, `S`, and `C`, both blocker
directions, the canonical multiplicity vector, and both independent validator
outputs if a SAT survivor occurs.

`UNKNOWN`: the experiment is not promoted to a proof that `m(2,4)=12`.
Although the arbitrary-finite-`U` reduction below is proved, this gate does
not contain an independently checkable exhaustive certificate such as DRAT
and does not contain a second complete search implementation. The UNSAT rows
therefore remain `COMPUTED`, are not a proof dependency, and do not authorize
P0054-C20, a stronger global `sat(7)` bound, publication, or a later gate.

## Arbitrary finite ground-set reduction

`PROVED`: let `H` be either side of an admissible pair and let `T` be in
`B(H)`. For each `x` in `T`, minimality of `T` gives a private row `E_x` in
`H` such that `T intersect E_x={x}`. Distinct elements of `T` have distinct
private rows, so `|T|<=|H|`. Hence every member of `mathcal S` has size at
most `b`, and every member of `mathcal C` has size at most `a`. The requested
lower bounds also force `a>=4` and `b>=2`, giving exactly the 15 searched
splits:

```text
total 9:  (7,2), (6,3), (5,4), (4,5)
total 10: (8,2), (7,3), (6,4), (5,5), (4,6)
total 11: (9,2), (8,3), (7,4), (6,5), (5,6), (4,7).
```

`PROVED`: choose the side with fewer members as the primary clutter `H`;
at `(5,5)` choose `mathcal S`, whose blocker minimum is four. Delete elements
of `U` that occur in no primary row. Such elements cannot occur in an
inclusion-minimal transversal. Every remaining element has one nonzero
incidence pattern in `{1,...,2^r-1}`, where `r=|H|`. Equal patterns are kept
with an exact positive integer multiplicity. Thus repeated patterns are not
lost, empty pattern classes are allowed, row sizes may be nonuniform, and
column order is removed without replacing actual blocker subsets by weighted
tuples. The private-row bound caps every primary row and every pattern
multiplicity, so this is a finite search for every arbitrary finite `U`.

`PROVED`: a minimal transversal contains at most one element from an
incidence class, because either of two equal-pattern elements could be deleted
while the other preserves all rows hit. Its pattern set is therefore an
inclusion-minimal cover of the `r` rows. Conversely, selecting one actual
element from every pattern in a minimal pattern cover gives a minimal
transversal. A cover `Q` contributes exactly

```text
product(m_q for q in Q)
```

actual blocker subsets. The search uses this exact integer count. It uses no
floating-point arithmetic.

`PROVED`: when a new incidence pattern is added, every old minimal pattern
cover remains minimal. Every new minimal cover contains the new pattern.
The incremental cover cache therefore enumerates exactly the old covers plus
the newly formed covers. A support with a cover below the required blocker
minimum can never be repaired by adding more patterns. A support with more
than the required blocker count already has too many realised blockers,
because all positive multiplicities are at least one. Increasing a
multiplicity can only increase the exact weighted count. These are sound
monotone pruning rules.

`PROVED`: primary-row permutations do not change the represented clutter
up to row labels. Complete survivors are quotiented by the lexicographically
least multiplicity vector over all `r!` row permutations. Mutual-blocker
involution for finite clutters means only one orientation of each ordered
split must be searched: using `mathcal C` as primary when `b<a`, or
`mathcal S` when `a<=b`, represents the same candidate pair and avoids a
duplicate oriented computation. Every ordered `(a,b)` still has its own
explicit result row.

`COMPUTED`: every branch in this run was rejected by a proved monotone partial
test before a complete degree vector reached the row-canonicalization stage.
Accordingly every `complete_degree_vectors` and `canonical_representatives`
counter is zero. This makes the final row-symmetry stage vacuous in this run;
it does not omit a split or import an old total-9/10 conclusion.

## Independent semantic validation

`COMPUTED`: the source contains two independent blocker implementations:

1. `blocker_powerset` scans the complete ground-set powerset and directly
   filters inclusion-minimal hitting sets.
2. `blocker_choice_minimization` enumerates one chosen point per hyperedge and
   minimizes the resulting unions. It does not scan the powerset and does not
   use incidence patterns.

`COMPUTED`: the two blocker engines agreed on all 199 clutters on ground sizes
zero through four, including the empty family and singleton empty-edge family.
Both reproduced blocker involution on every case. On all 194 nonempty-family
cases, the direct pattern-cover formula agreed with explicit blocker
cardinality and member-size multiset.

`COMPUTED`: on those same 194 nonempty cases, the incremental cover cache
agreed with the original combination-based cover enumerator, and the
three-argument `weighted_cover_count(covers, multiplicities, cap)` API was
executed and agreed with the original engine. This check was added after a
read-only concurrent audit reported a stale intermediate four-argument call;
the final saved source contains only the checked three-argument calls.

`UNKNOWN`: these two validators independently check blocker semantics and
the incremental formula on all stated small cases. They are not a second
complete implementation of the 15-split exhaustive search.

## Exact split results

`COMPUTED`:

| total | `(a,b)` | primary | DFS nodes | elapsed seconds | status |
|---:|---:|:---:|---:|---:|:---|
| 9 | `(7,2)` | `C` | 40 | 0.000093 | `UNSAT_COMPUTED` |
| 9 | `(6,3)` | `C` | 2,329 | 0.008291 | `UNSAT_COMPUTED` |
| 9 | `(5,4)` | `C` | 129,443 | 0.464629 | `UNSAT_COMPUTED` |
| 9 | `(4,5)` | `S` | 29,314 | 0.034417 | `UNSAT_COMPUTED` |
| 10 | `(8,2)` | `C` | 47 | 0.000049 | `UNSAT_COMPUTED` |
| 10 | `(7,3)` | `C` | 3,383 | 0.005724 | `UNSAT_COMPUTED` |
| 10 | `(6,4)` | `C` | 341,505 | 1.362560 | `UNSAT_COMPUTED` |
| 10 | `(5,5)` | `S` | 5,545,988 | 12.337668 | `UNSAT_COMPUTED` |
| 10 | `(4,6)` | `S` | 68,278 | 0.078559 | `UNSAT_COMPUTED` |
| 11 | `(9,2)` | `C` | 53 | 0.000052 | `UNSAT_COMPUTED` |
| 11 | `(8,3)` | `C` | 5,047 | 0.008456 | `UNSAT_COMPUTED` |
| 11 | `(7,4)` | `C` | 723,122 | 3.159503 | `UNSAT_COMPUTED` |
| 11 | `(6,5)` | `C` | 114,833,182 | 1078.980734 | `UNSAT_COMPUTED` |
| 11 | `(5,6)` | `S` | 25,514,100 | 67.415258 | `UNSAT_COMPUTED` |
| 11 | `(4,7)` | `S` | 144,980 | 0.173735 | `UNSAT_COMPUTED` |

`COMPUTED`: the run visited 147,340,811 DFS nodes in total. The complete
recorded run took 1164.177798 seconds. The longest split was `(6,5)` at
1078.980734 seconds, below the 7200-second per-split limit. No split timed out.

## Run provenance and abandoned non-evidence

`COMPUTED`: two development runs were manually abandoned and are not evidence:

1. The first run was interrupted during `(6,5)` after profiling showed that
   it repeatedly recomputed all minimal pattern covers. Its redirected JSON
   remained empty, and no status or counter from it was imported. The source
   was changed to the proved incremental cover cache.
2. A later optimized run was interrupted during `(6,5)` after a concurrent
   audit reported a possible stale four-argument leaf call. Its output was
   discarded even though the then-current disk source already showed the
   correct three-argument call. The explicit 194-case incremental/API
   self-test was added before starting the final run from total 9 again.

`COMPUTED`: the only result record used here is the subsequent complete run
of final source SHA-256

```text
50a1016029f1b57138a9209adbe6cd1d22a1a759cc802a9df3e6dc3ebf78fe58
```

No totals, statuses, wall times, or conclusions were imported from G4.3 or
from either abandoned G4.4 run.

## Deterministic replay

`COMPUTED`: commands:

```text
UV_OFFLINE=1 uv run --offline python \
  Problems/P0054/experiments/g4.4-exact-local/search.py \
  --totals 9 10 11

UV_OFFLINE=1 uv run --offline python \
  Problems/P0054/experiments/g4.4-exact-local/search.py \
  --totals 9 10 11 \
  --verify-results \
  Problems/P0054/experiments/g4.4-exact-local/results.json
```

`COMPUTED`: the full second run ended with
`STRUCTURAL_REPLAY_MATCH_COMPUTED`. The replay projection ignores only wall
times and process resource measurements. It compares source and frozen-input
hashes, coverage boundaries, both semantic validator records, every split
status, completion flag, witness field, orientation, and every structural
counter. The canonical JSON encoding of the matched stable projection has
SHA-256:

```text
995d635cc94b6c28188d60ed866f2e332826a55f3736b54096c2a9bc8f068f4c
```

## Environment and resource boundary

`COMPUTED`:

```text
NETWORK: OFFLINE
RANDOM_SEED: NONE_DETERMINISTIC_EXHAUSTIVE_ENUMERATION
HEAD: d2c8e3eb81466a3743c736319ef1874920590abc
Python under uv: 3.12.13
uv: 0.11.29 (Homebrew 2026-07-15 aarch64-apple-darwin)
OS: macOS 27.0 build 26A5378n arm64
per-split limit: 7200 seconds
temporary-disk limit: 30 GB
peak RSS reported by final Python run: 28,082,176 bytes
search CNF/solver database bytes: 0
```

`COMPUTED`: the experiment used no network, SAT/SMT solver, old size-54 CNF,
Formalizer, random seed, floating point, or external proof output. The search
engine created no temporary CNF or solver database. Shell-captured JSON files
were only tens of kilobytes, so temporary usage remained far below 30 GB.

`COMPUTED`: frozen inputs were checked before the final source was written.
In particular:

```text
AGENTS.md
  5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1
G4.4 section0-freeze.md
  b06600a748f39f1a5d09b0a7980e90cd717a8878d1059d9a86deb7700dacdd3d
G4.4 frozen-subproblem.md
  e0dd5370eb639cd678bff60e7b17e0d025758a99c2648bc99d95d197924b78c7
G4.4 literature freeze-manifest.json
  765b79a3832c03e03903045286be1fa8f05f714dee1381e6a5d34a2b067954e5
G4.3 search.py
  ce1026519f6e9f7b3a90da6bd0ea7e1eb7fc6d6b0f7db2cadda05262488b7ec0
G4.3 results.json
  315a9daea8ab4c1f28e03fdc8d17c1478bdb1ac0a1a28b4ec5fe7bf65b51d095
G4.3 report.md
  93084dec2231b05d33fe4d66e585a809261961a0b6a9d10006796f42cfc387fb
```

`COMPUTED`: no G4.4 Prover or Referee output was read or contacted.

## Limitations

`UNKNOWN`: this experiment does not establish the conjectured product
inequality `|mathcal S||mathcal C|>=32`, does not provide a DRAT-style
certificate, does not provide a second exhaustive implementation, and does
not settle novelty or current literature status.

`UNKNOWN`: without those additional proof-grade dependencies and the required
isolated Referee gate, `m(2,4)=12` remains unproved here. The correct stopping
point is the 15-row `UNSAT_COMPUTED` artifact set.
