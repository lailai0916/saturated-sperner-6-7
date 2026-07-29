# P0054 G4.3 mutual-blocker incidence search

## Scope and verdict

`DEFINITION`: the searched objects are ordinary finite clutters
`(mathcal S, mathcal C)` on an arbitrary finite `U` with

```text
mathcal S = B(mathcal C),  mathcal C = B(mathcal S),
min_{S in mathcal S}|S| >= 2,  min_{C in mathcal C}|C| >= 4.
```

`COMPUTED`: exact incidence-pattern enumeration found no admissible pair for
any split with `a=|mathcal S|`, `b=|mathcal C|`, and `a+b` equal to 8, 9, or
10.  Every one of the 12 searched splits has status `UNSAT_COMPUTED` in
`results.json`.  There is therefore no SAT witness to report.

`UNKNOWN`: this experiment is not a general lower-bound proof, is not a proof
dependency, and makes no claim about any total outside exactly 8, 9, and 10.
It does not promote a global `sat(7)` bound, solve the frozen theorem, establish
novelty, or authorize a later gate.

## Finite coverage reduction

`PROVED`: if `T` is in `B(H)`, then every `x` in `T` has a distinct private
witness `E_x` in `H` satisfying `T intersect E_x = {x}`.  Indeed, minimality
of `T` says `T minus {x}` fails to hit some `E_x` in `H`.  Since `T` does hit
`E_x`, their intersection is exactly `{x}`.  If `x != y` and `E_x=E_y`, the
same intersection would be both `{x}` and `{y}`, a contradiction.  Thus
`x -> E_x` is injective and `|T| <= |H|`.  The empty `T` case is immediate;
under the frozen convention `B(empty family)={empty set}`, it is also
consistent with the empty-family boundary.

`PROVED`: in an admissible pair, the private-witness bound gives
`2 <= |S| <= b` for every `S` and `4 <= |C| <= a` for every `C`.  Hence
`a>=4`, `b>=2`, and the complete split list for the requested totals is

```text
8:  (6,2), (5,3), (4,4)
9:  (7,2), (6,3), (5,4), (4,5)
10: (8,2), (7,3), (6,4), (5,5), (4,6).
```

`PROVED`: choose the side with fewer members as the primary hypergraph `H`
(using `mathcal S` at the tie `(5,5)`).  Delete elements in no member of `H`;
they can occur in no inclusion-minimal transversal.  Every remaining element
is represented by its nonzero incidence pattern in `{1,...,2^r-1}`, where
`r=|H|`.  Equal patterns are stored by an exact positive multiplicity, which
quotients column order while retaining repeated patterns.  The row-size upper
bounds above bound every multiplicity and the total active incidences by
`a*b`.  Row permutations are quotiented by the lexicographically minimum
multiplicity vector over all `r!` permutations.

`PROVED`: a minimal transversal cannot contain two elements with the same
incidence pattern, since deleting either copy preserves exactly the rows hit
by the other.  Consequently its pattern set is an inclusion-minimal cover of
all rows.  Conversely, choosing one real element from each pattern of a
minimal pattern cover produces a minimal transversal.  A pattern cover `Q`
therefore contributes exactly `product(m_q for q in Q)` blocker members.  The
search uses this exact integer formula; it uses no floating point.

`PROVED`: the partial blocker-count pruning is sound.  When a new incidence
pattern is added, every old minimal pattern cover remains a minimal cover, and
each old realised transversal remains minimal because unchosen new elements
cannot repair deletion of one of its chosen elements.  Thus the weighted
blocker count from the current support is a monotone lower bound.  Any branch
already exceeding the required blocker count cannot have an admissible
extension.  In this run every branch died at this stronger labelled-space
test, before a complete survivor reached row canonicalization.  The zero
`canonical_representatives` counters therefore mean that the canonical stage
was vacuous, not that a split was omitted.

## Independent semantic validation

`COMPUTED`: two independent blocker implementations are included:

1. `blocker_powerset` scans the full ground-set powerset and directly filters
   inclusion-minimal hitting sets.
2. `blocker_choice_minimization` independently enumerates one chosen point per
   hyperedge and minimizes the resulting unions; it does not scan the powerset
   and does not use incidence patterns.

`COMPUTED`: the engines agreed on all 199 clutters on ground sizes 0 through 4,
including the empty family and singleton empty-edge family.  On the 194
nonempty-family cases, the independent engines also agreed with the weighted
incidence-pattern formula on blocker cardinalities and member-size multisets.
Both engines reproduced blocker involution on every tested clutter.  Because
the requested search had no SAT case, no `U/S/C` witness exists; the source is
prepared to save a complete witness, canonical vector, and both validator
results if a SAT survivor occurs.

## Exact results

`COMPUTED`:

| total | splits | result |
|---:|---|---|
| 8 | `(6,2)`, `(5,3)`, `(4,4)` | all `UNSAT_COMPUTED` |
| 9 | `(7,2)`, `(6,3)`, `(5,4)`, `(4,5)` | all `UNSAT_COMPUTED` |
| 10 | `(8,2)`, `(7,3)`, `(6,4)`, `(5,5)`, `(4,6)` | all `UNSAT_COMPUTED` |

`COMPUTED`: exact per-case counters are stored in `results.json`; the largest
case `(5,5)` visited 5,545,988 DFS nodes and
took 26.922554458025843 seconds.  The complete recorded run took
31.061589249991812 seconds.  An earlier unoptimized development run was
manually interrupted during `(5,5)` to add the proved monotone pruning; no
status from that interrupted run was imported.  `FIRST_INVALID_STEP: NONE`.

## Replay and resource record

`COMPUTED`: environment and command:

```text
NETWORK: OFFLINE
RANDOM_SEED: NONE_DETERMINISTIC_EXHAUSTIVE_ENUMERATION
Python: 3.12.13
uv: 0.11.29 (Homebrew 2026-07-15 aarch64-apple-darwin)
UV_OFFLINE=1 uv run --offline python Problems/P0054/experiments/g4.3-stronger-lower/search.py --totals 8 9 10
UV_OFFLINE=1 uv run --offline python Problems/P0054/experiments/g4.3-stronger-lower/search.py --totals 8 9 10 --verify-results Problems/P0054/experiments/g4.3-stronger-lower/results.json
```

`COMPUTED`: no SAT/SMT solver, old size-54 CNF, network access, or Formalizer
was used.  The longest completed case was under 27 seconds, below the 3600
second per-solver limit.  The experiment created no temporary CNF or solver
database; the experiment directory occupied 36 KiB before this report and
manifest, far below 20 GB.

`COMPUTED`: frozen-input hashes independently checked before the search:

```text
AGENTS.md                                                           5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1
Problems/P0054/experiments/g4.3-stronger-lower/section0-freeze.md    759e7b6a2bbad8853f2baa7424c8b19ac06e6ecaf07b3c3758a30d57a9a99aaf
Problems/P0054/proof/g4.3-stronger-lower/frozen-subproblem.md        cc64e1e376196355b68266abcfdf228d38836b6fc05c170204397efc67a8ddaa
```

`COMPUTED`: current artifact hashes before adding the manifest:

```text
search.py    ce1026519f6e9f7b3a90da6bd0ea7e1eb7fc6d6b0f7db2cadda05262488b7ec0
results.json 315a9daea8ab4c1f28e03fdc8d17c1478bdb1ac0a1a28b4ec5fe7bf65b51d095
```
