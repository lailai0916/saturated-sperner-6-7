# P0054 G4.2 isolated Experimentalist report: seven-member `A_2`

## Scope and evidence boundary

- `DEFINITION`: this is the isolated compatible Experimentalist run for
  `P0054_G4_2_INTERNAL_LAYER_EQUALITY_CLASSIFICATION`. The dedicated role
  launcher failed before reading task materials; no G4.2 Prover output was
  read.
- `DEFINITION`: no network, Formalizer, size-54 CNF, old-file modification,
  status/claims update, commit, push, or publication action was used.
- `COMPUTED`: every SAT/UNSAT and incidence-quotient conclusion below is
  finite exact computation or human-audited executable reduction.
- `UNKNOWN`: there is no external UNSAT certificate and no formal arbitrary-
  `U` reduction. This report therefore does not label `|A_2|>=8` as `PROVED`
  or `FORMALIZED`.

## Exact model

`DEFINITION`: write the seven members as `a` small generators `S_i` and `b`
large members with complements `C_j=U\K_j`, where `a+b=7`. The model checks:

1. `|S_i|>=2` and `|C_j|>=4`;
2. the `S_i` form a clutter and the `C_j` form a clutter (equivalently, the
   corresponding large traces form an antichain);
3. every `S_i` intersects every `C_j`, equivalently `S_i` is not contained in
   the associated large trace;
4. for every `R subseteq U`, some `S_i subseteq R` or some `R cap C_j=empty`.

The fourth condition is exactly the frozen oriented saturation condition.
The script uses Boolean membership variables rather than selecting from a
pre-enumerated family of masks.

## Exact splits and canonical labeling

`COMPUTED`: blocker duality in the model eliminates all splits except

```text
(a,b)=(4,3) and (a,b)=(5,2).
```

The reasons are included split-by-split in `results.json`: a complement in
the blocker of an `a`-edge clutter has a representative of size at most `a`,
so `a>=4`; a small blocker of a one-edge complement family is a singleton,
so `b>=2`.

`DEFINITION`: the SMT search removes ground-set symmetry by sorting columns
by their complete seven-bit incidence code. It removes safe member symmetry
by sorting small rows and complement rows by cardinality. Any SAT model would
then be canonically relabeled again by exhausting the at most `a!b!` row
permutations, sorting equal-incidence columns, and choosing the
lexicographically least form.

`DEFINITION`: a SAT row would contain the full ground size, small masks and
sets, complement masks and sets, derived large-trace masks, incidence-pattern
multiplicities, and both validator reports. No SAT row occurred in this run.

## Two independent semantic validators

`DEFINITION`: validator A directly enumerates every `R subseteq U`, checks the
oriented-cover multiplicity, all size restrictions, both same-side
antichains, and every cross-intersection.

`DEFINITION`: validator B independently enumerates all subsets, computes the
minimal transversals of the complement clutter and of the small clutter, and
checks the two blocker equalities.

`COMPUTED`: both validators accepted the positive control consisting of four
disjoint two-sets and all 16 of their four-point choice transversals. This is
a 20-member semantic control, not a seven-member witness. Both validators
rejected the negative control obtained by deleting one small edge. Validator
A recorded 27 explicit uncovered `R` masks; validator B recorded both blocker
mismatches. The complete masks and diagnostics are in `results.json`.

## Layer-by-layer finite search

`COMPUTED`: Z3 4.16.0 searched from `q=0` upward with `random_seed=0`, no
experiment randomness, and a 60,000 ms limit per solver call (well below the
3,600-second bound). Each `q` checks both surviving exact splits.

| `q=|U|` | `(a,b)=(4,3)` | `(a,b)=(5,2)` | combined result |
|---:|---|---|---|
| 0 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 1 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 2 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 3 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 4 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 5 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 6 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 7 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 8 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 9 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |
| 10 | `UNSAT` | `UNSAT` | `UNSAT_COMPUTED` |

No solver returned `UNKNOWN`. These bounded outcomes have no external proof
certificate and are not a global lower bound.

## Incidence-pattern quotient and multiplicity truncation

`DEFINITION`: coverage plus the two clutter conditions says exactly that the
small family is the family of minimal transversals (the blocker) of the
complement family, and conversely. Unused zero-incidence points can be
discarded. Points with the same full member-incidence signature form a
pattern class with an integer multiplicity.

`COMPUTED`: for `(a,b)=(4,3)`, every complement blocker has size at least four.
A four-edge small clutter therefore has transversal number four. Its four
small edges are forced pairwise disjoint: an intersection point plus one
point from each of the other two edges would otherwise be a transversal of
size at most three. After canonical relabeling, only singleton small-incidence
patterns `1,2,4,8` remain, with multiplicities `m_i>=2`. Every choice of one
point per small edge is a distinct minimal transversal, so the computed
blocker count is

```text
m_1 m_2 m_4 m_8 >= 2^4 = 16 > b=3.
```

Multiplicity can be truncated at two: increasing a class beyond two only
increases this product.

`COMPUTED`: for `(a,b)=(5,2)`, the two complements must be disjoint; an
intersection point would be a forbidden singleton small blocker. Their only
nonzero canonical complement-incidence patterns are `1,2`, with
multiplicities at least four. Every cross-pair is a distinct minimal
transversal, so

```text
m_1 m_2 >= 4^2 = 16 > a=5.
```

Multiplicity can be truncated at four for the same monotonic reason. Thus the
incidence quotient reports `UNSAT_COMPUTED_NO_EXTERNAL_CERTIFICATE` for
arbitrary finite `q`; this is stronger computational evidence than merely
increasing the raw `q` cutoff.

## First uncertain step and experimental conclusion

- `COMPUTED`: no genuine seven-member `A_2` model exists for `q=0,...,10` in
  the exact SMT model.
- `COMPUTED`: the blocker/incidence quotient eliminates every `a+b=7` split
  with threshold-capped multiplicities and reports no arbitrary-`q` model.
- `UNKNOWN`: the first unverified step is promotion of the general blocker
  equivalence and incidence/multiplicity reduction from audited prose and code
  to an externally certified or formal dependency-resolved theorem.
- `UNKNOWN`: absent that certification and a Prover/Referee gate, this report
  does not establish `THEOREM_A2_CANDIDATE`.

## Relation to P0054-C17

`DEFINITION`: frozen P0054-C17 is the accepted `sat(7)>=37` global lower
bound. Replacing its `|A_2|>=7` summand by an independently proved
`|A_2|>=8` would add exactly one and support the G4.2 fallback target
`sat(7)>=38`. This Experimentalist output neither modifies C17 nor promotes a
new claim.

## Environment, commands, replay, and resources

- `COMPUTED`: Python 3.12.13 (CPython), Z3 4.16.0,
  `macOS-27.0-arm64-arm-64bit`.
- `DEFINITION`: random seed `NONE`; Z3 `random_seed=0`.
- `DEFINITION`: no temporary artifact approached 20 GB; raw JSON is under
  20 KB and the experiment used no size-54 CNF.

Exact output command:

```bash
UV_OFFLINE=1 uv run python \
  Problems/P0054/experiments/g4.2-stronger-lower/exact_a2_search.py \
  --q-max 10 --timeout-ms 60000 \
  > /tmp/p0054-g42-results.json
```

Byte replay command:

```bash
UV_OFFLINE=1 uv run python \
  Problems/P0054/experiments/g4.2-stronger-lower/exact_a2_search.py \
  --q-max 10 --timeout-ms 60000 \
  | diff -u \
    Problems/P0054/experiments/g4.2-stronger-lower/results.json -
```

The recorded replay returned exit status zero. `manifest.json` records the
SHA-256 digests of the script, exact JSON, and this report; it deliberately
does not hash itself.
