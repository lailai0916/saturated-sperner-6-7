# P0054 G4 offline Experimentalist report

## Scope and evidence boundary

- `DEFINITION`: role is the isolated offline Experimentalist for
  `P0054_G4_GLOBAL_LOWER_BOUND_FOR_sat7`.
- `DEFINITION`: no network access was used. The frozen G4 literature pack and
  pre-G4 definitions/code were readable; no
  `proof/g4-global-lower/attempt-*.md` file was read.
- `COMPUTED`: every result in this report is an exact-arithmetic or bounded
  finite-model result. No finite-core `UNSAT` result below has an external
  proof certificate, and none is promoted to a global theorem.
- `UNKNOWN`: this experiment does not determine `sat(7)`, prove
  `sat(7) >= 37`, or prove any new global lower bound.

## Exact model checked

`DEFINITION`: for a core of size `q` and internal layer `i`, a selected small
mask `S` is eligible only when `|S| >= i`; a selected large-core mask `L` is
eligible only when `q-|L| >= 6-i`. The SMT model imposes:

1. no comparable selected pair (small/small, large/large, or `S subset L`);
2. for every core mask `R`, at least one selected event `S subset R` or
   `R subset L`;
3. the requested upper bound on the number of selected events.

This is the finite common-atom oriented-coverage model. Core sizes are exactly
`q=0,...,7`; it is not an exhaustive search over arbitrary ground-set size.

## Exact rational probability checks

`COMPUTED`: `fractions.Fraction` gives the following values without floating
point arithmetic.

| Layer | `p` | small event cap | large event cap | max cap | six-event maximum | exact reciprocal ceiling |
|---|---:|---:|---:|---:|---:|---:|
| `A2` | `2/5` | `4/25` | `81/625` | `4/25` | `24/25` | `7` |
| `A3` | `1/2` | `1/8` | `1/8` | `1/8` | `3/4` | `8` |
| `A4` | `3/5` | `81/625` | `4/25` | `4/25` | `24/25` | `7` |

`COMPUTED`: for every eligible individual event on every core size `0,...,7`,
the program independently enumerated all Bernoulli-weighted core masks at all
three parameters and matched the formula `p^|S|` or
`(1-p)^(q-|L|)`. It checked 2,850 weighted identities.

## Middle-layer equality audit

`COMPUTED`: at `p=1/2`, an eight-event equality case would require eight
events of weight exactly `1/8` and coverage multiplicity exactly one at each
core mask. On `q=0,...,7`, the program exhaustively checked the relevant event
geometry:

- every two distinct small upper events intersect at the union of their masks;
- every two distinct large lower events intersect at the intersection of their
  masks;
- a small upper event and large lower event overlap exactly when `S subset L`,
  which is precisely the forbidden cross-comparability condition.

The audit counted 17,226 small-pair intersections, 17,226 large-pair
intersections, and 30,049 cross-event equivalences. Thus the finite
equality-reduced model permits at most one event of each side, not eight, for
all checked `q`. This is `COMPUTED` finite evidence only; the general equality
exclusion belongs to a Prover, not this report.

## Boundary cases

`COMPUTED`: all 950 eligible members cover their own core mask in the event
model. The source size restrictions exclude a small empty mask and a large
full-core mask. Consequently, in every checked core, an empty small side fails
coverage at the full core and an empty large side fails coverage at the empty
core.

`COMPUTED`: explicit regression witnesses in `results.json` record:

- two eligible middle small events on `q=4` overlapping at mask `15`;
- two eligible middle large events on `q=4` overlapping at mask `0`;
- a cross overlap on `q=6` when the required antichain condition is removed
  (`S=L=7`, overlap mask `7`). This last witness violates the antichain and is
  not a counterexample to the proposed equality exclusion; it verifies that
  the antichain hypothesis is essential.

No counterexample to the checked event identities or equality implications was
found in the recorded finite scope.

## SMT search results

`COMPUTED`: Z3 4.16.0, with a 5,000 ms limit per test and solver seed `0`,
returned:

| Layer | target | `q=0,...,6` | `q=7` |
|---|---:|---|---|
| `A2` | at most `6` | all `UNSAT` | `UNSAT` |
| `A2` | at most `7` | all `UNSAT` | `UNSAT` |
| `A3` | at most `8` | all `UNSAT` | `UNKNOWN` (timeout) |
| `A4` | at most `6` | all `UNSAT` | `UNSAT` |
| `A4` | at most `7` | all `UNSAT` | `UNSAT` |

These outcomes search both empty-side cases automatically. The `A3,q=7`
timeout is retained as `UNKNOWN`. The other `UNSAT` values are bounded solver
outputs without external certificates; in particular, the absence of a
seven-member `A2`/`A4` model through `q=7` is not a lower bound for arbitrary
`q`.

## Environment, command, and replay

- `COMPUTED`: Python `3.12.13` (CPython), Z3 `4.16.0`, platform string
  `macOS-27.0-arm64-arm-64bit`.
- `DEFINITION`: experiment random seed `NONE`; Z3 `random_seed=0`.
- `DEFINITION`: per-test timeout `5000` ms, below the required 60-second cap.
- `DEFINITION`: the JSON written to `results.json` is the exact stdout of:

```bash
UV_OFFLINE=1 uv run python Problems/P0054/experiments/g4-global-lower/exact_layer_search.py \
  --q-max 7 --timeout-ms 5000
```

`COMPUTED`: independent replay was run and byte-compared successfully:

```bash
UV_OFFLINE=1 uv run python Problems/P0054/experiments/g4-global-lower/exact_layer_search.py \
  --q-max 7 --timeout-ms 5000 \
  | diff -u Problems/P0054/experiments/g4-global-lower/results.json -
```

The replay produced no diff and exit status `0`.

## Files and integrity

The SHA-256 manifest is `manifest.json`. It covers the script, exact stdout
JSON, and this report. The manifest deliberately does not hash itself.

## Experimental conclusion

- `COMPUTED`: the proposed exact rational caps and integer ceilings were
  reproduced.
- `COMPUTED`: the requested equality-event, empty-side, empty/full-mask,
  member-self, same-side-intersection, and cross-overlap checks passed on
  cores `q=0,...,7`.
- `COMPUTED`: no eight-member middle-layer model was found for `q<=6`; the raw
  `q=7` search timed out, while the equality-reduced event audit passed through
  `q=7`.
- `COMPUTED`: no at-most-seven second/fourth-layer model was found for
  `q=0,...,7`.
- `UNKNOWN`: no global conclusion follows from these bounded computations.
