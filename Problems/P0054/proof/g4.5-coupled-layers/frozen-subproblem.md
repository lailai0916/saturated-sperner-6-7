# P0054 G4.5 coupled-layer equality problem

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_5_COUPLED_LAYER_EQUALITY
PRIMARY_QUESTION: can total canonical size 47 occur?
TARGET_IF_EXCLUDED: sat(7) >= 48
NETWORK: OFFLINE
```

## Frozen input

`PROVED`: P0054-C20 gives the eventual stable bounds

```text
47 <= sat(7) <= 55
```

and the independent canonical-layer bounds

```text
(|A_0|,...,|A_6|) >= (1,6,12,9,12,6,1).
```

`PROVED`: the second and fourth layers each induce an admissible `(2,4)`
mutual-blocker pair of total size at least twelve. The exact local parameter is
`m(2,4)=12`. The two layers share the same finite trace ground set and arise in
one canonical decomposition, but the accepted proof applies the local bound to
them independently.

`PROVED`: every member of `A_i`, for `i>0`, has a strict predecessor in
`A_(i-1)`, and every member of `A_i`, for `i<6`, has a strict successor in
`A_(i+1)`. Every layer is a saturated antichain, the layers are pairwise
disjoint, and all use the same all-or-none block `H`.

All G0--G4.4 artifacts and manifests are immutable inputs. P0054-C5 and
P0054-C9 remain `UNKNOWN`. Exact `sat(7)`, novelty, and priority remain
`UNKNOWN`.

## One objective

Determine whether equality in the seven independent layer bounds can hold
simultaneously. In particular, a total-47 family would force

```text
(|A_0|,...,|A_6|) = (1,6,12,9,12,6,1).
```

Analyze the compatibility of the equality cases for `A_2`, `A_3`, and `A_4`
under the actual predecessor, successor, disjointness, antichain, and common-`H`
constraints. Use `A_1` and `A_5` equality constraints when they provide useful
coupling. Do not assume that a twelve-member blocker pair is isomorphic to the
known two-disjoint-four-cycles witness; G4.4 did not prove such uniqueness.

The preferred successful outcome is a dependency-closed arbitrary-finite-ground-
set proof that total 47 is impossible, which would give the candidate theorem
`sat(7)>=48`. A complete jointly compatible total-47 construction or a precise
counterexample to a proposed coupling lemma is also genuine progress. Preserve
the first failed proof step when a route breaks.

## Evidence boundary

- Exact combinatorial arguments must allow arbitrary finite trace ground sets,
  repeated incidence patterns, nonuniform member sizes, and empty incidence
  classes.
- A bounded SAT/SMT search, sampled computation, timeout, or solver failure is
  `COMPUTED`, never a global lower bound.
- Do not infer global equality-case structure from the single G4.4 upper witness.
- Do not alter claims or status unless a dependency-closed theorem is obtained
  and independently checked in a later authorized referee gate.
- Do not formalize, publish, push, contact experts, make novelty claims, or start
  a second research objective in this turn.

## Allowed output

Write only under `Problems/P0054/proof/g4.5-coupled-layers/` and, if a bounded
experiment is essential, `Problems/P0054/experiments/g4.5-coupled-layers/`.
Create one factual local checkpoint commit only when mathematical artifacts
change.
