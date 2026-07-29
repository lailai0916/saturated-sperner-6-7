# P0054 exact-value formalization crosswalk

Evidence date: 2026-07-27.

## Frozen mathematical input

The formalization is bound to
`Problems/P0054/experiments/certificates/core-8-target-55-selfcontained.json`,
whose candidate semantic SHA-256 is
`55d0a1e19a024efb944fc9a00ea466bdd6d5b11383f1bd86c1f772d8fb92acac`.
The independent expanded-family SHA-256 is
`8277267a7a9cbc6040432a9d6ffc3f16c540a6013b78bedbd85e6b1e27adde0f`.

The eight core points occupy bits `0,...,7`.  The three-point homogeneous
block occupies bits `8,9,10`.  Thus the smallest expanded ground is `Fin 11`.
Source labels `1,...,11` correspond to Lean values `0,...,10`.

## Exact correspondence

- `size55Masks` contains exactly the 55 expanded source masks.
- `size55LayerMasks` has sizes `(1,6,12,17,12,6,1)` and its flattened
  `Finset` equals `size55Masks`.
- `size55` is the image of those masks under the eleven-bit decoder.
- `size55_card` proves that the image has exactly 55 distinct members.
- `size55_layerUnion` proves that the seven displayed Lean layers have union
  exactly `size55`.

The executable regression test compares the Lean mask set with the frozen
candidate member by member as a set and checks all recorded file hashes.

## Finite-certificate scope

The Lean theorem formalizes the concrete `Fin 11` realization.  It does not
formalize the parameterized replacement of the three-point block by every
larger homogeneous block by itself. The later `Parameterized55` and stable
bridge modules perform that step. Thus this finite certificate is a proper
subtheorem of the final exact-value formalization.

## Stable predicate

| Natural object or claim | Lean declaration |
|---|---|
| exact minimum on `Fin n` | `AiMathLab.SaturatedSperner.IsSaturationNumberAt` |
| eventual exact minimum | `AiMathLab.SaturatedSperner.IsStableSaturationNumber` |

`IsStableSaturationNumber k s` means that some `N` satisfies
`IsSaturationNumberAt k n s` for every `n>=N`. The inner predicate contains
both a family of cardinality `s` and a lower bound for every saturated family.
This is a proposition with an existential threshold, not a numerical function
evaluation.

## Exact sat(6) theorem

| Natural object or claim | Lean declaration |
|---|---|
| finite row family | `AiMathLab.P0054.G413.Hypergraph` |
| minimal-transversal blocker | `AiMathLab.P0054.G413.blocker` |
| every row has size at least `r` | `AiMathLab.P0054.G413.RowsCardAtLeast` |
| explicit five-member size-two side | `AiMathLab.P0054.Sat6.witnessSmall` |
| explicit four-member size-three side | `AiMathLab.P0054.Sat6.witnessLarge` |
| both witness blocker equalities | `witness_blocker_large`, `witness_blocker_small` |
| witness total cardinality nine | `witness_total_card` |
| three-row blocker lower bound seven | `threeRow_blocker_card_ge_seven` |
| four-row blocker lower bound six | `fourRow_blocker_card_ge_six` |
| arbitrary-finite-ground total lower bound nine | `local_lower` |
| parameterized 30-member family | `AiMathLab.P0054.Sat6Parameterized30.family` |
| parameterized cardinality and saturation | `AiMathLab.P0054.Sat6Parameterized30.family_card`, `AiMathLab.P0054.Sat6Parameterized30.family_saturated` |
| finite-ground lower bound 30 | `AiMathLab.P0054.Sat6Exact.family_card_lower` |
| transported construction on `Fin n` | `AiMathLab.P0054.Sat6StableExact.construction_certificate` |
| exact eventual value | `AiMathLab.P0054.Sat6StableExact.sat_six_eq_thirty` |

`local_lower` assumes both input families are clutters, both blocker
equalities, and the two member-size minima. These are exactly the natural
admissibility hypotheses. Combined with the explicit witness declarations,
it is a kernel-checked representation of `m(2,3)=9`.

The final declaration has type `IsStableSaturationNumber 6 30`. Its witness
threshold is `3*2^30`. Hence it formalizes attainment and optimality on every
labelled finite ground past that threshold.

## Exact sat(7) theorem

| Natural object or claim | Lean declaration |
|---|---|
| parameterized 55-member family | `AiMathLab.P0054.Parameterized55.family` |
| parameterized size, saturation, and atom | `AiMathLab.P0054.Parameterized55.full_certificate` |
| transported construction on `Fin n` | `AiMathLab.P0054.Sat7StableBridge.construction_certificate` |
| canonical finite-ground lower bridge | `AiMathLab.P0054.SevenFanoBridge.family_card_lower_of_fano_adjacent` |
| final Fano-adjacent exclusion | `AiMathLab.P0054.FanoAdjacentClosed.fano_adjacent_impossible` |
| exact eventual value | `AiMathLab.P0054.Sat7StableExact.sat_seven_eq_fifty_five` |

The final declaration has type `IsStableSaturationNumber 7 55`. Its witness
threshold is `3*2^55`. The lower-bound dependency graph includes the complete
canonical reduction and all remaining middle and Fano-adjacent exclusions.

## G4.13 exact-value subproblem

| Natural object or claim | Lean declaration |
|---|---|
| G4.13 row family | `AiMathLab.P0054.G413.Hypergraph` |
| G4.13 blocker | `AiMathLab.P0054.G413.blocker` |
| admissible five-row kernel completion | `AiMathLab.P0054.G413.IsKernelCompletion` |
| unconditional five-row residual bound | `AiMathLab.P0054.G413.residualLemma2` |
| exclusion of all five pair-graph shapes | `AiMathLab.P0054.G413.fiveRow_eight_blocker_impossible` |
| no admissible eight-row completion | `AiMathLab.P0054.G413.no_kernel_completion_of_eight` |

The final declaration matches the local five-row degree-three subproblem in
the G4.12 `(8,8)` branch. It quantifies over an arbitrary finite ground set
and does not impose a finite-core bound.

G4.13 was a local formalization milestone. The later exact-value modules
formalize the remaining branches and connect them to the stable predicate.

## Verification gate

- `lake build AiMathLab AiMathLab.P0054Sat7StableExact` passed 17488 jobs.
- `lake env lean Problems/P0054/formal/Main.lean` passed.
- Both final theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- The forbidden token and bypass scan over Lean sources returned zero hits.

The exact stable-value claims P0054-C23 and P0054-C28 are `FORMALIZED`.
P0054-C5, P0054-C9, P0054-C24, and P0054-C29 remain `UNKNOWN` because Lean
does not establish novelty or publication priority.
