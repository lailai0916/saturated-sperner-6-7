# P0054 Lean formalization report

## Result

Evidence date: 2026-07-27.

Lean accepts the two final public theorems:

- `AiMathLab.P0054.Sat6StableExact.sat_six_eq_thirty :
  IsStableSaturationNumber 6 30`;
- `AiMathLab.P0054.Sat7StableExact.sat_seven_eq_fifty_five :
  IsStableSaturationNumber 7 55`.

Both exact eventual statements are `FORMALIZED`.

## Stable-number semantics

`IsStableSaturationNumber k s` expands to an existential threshold. For every
`n` past that threshold, it includes both clauses below:

- a saturated `k`-Sperner family of cardinality `s` exists on `Fin n`;
- every saturated `k`-Sperner family on `Fin n` has cardinality at least `s`.

The final declarations prove propositions with these quantifiers. They do not
evaluate a Lean numerical function named `sat`.

## Concrete size-55 certificate

Lean also accepts the following finite-certificate theorems:

- `size55_card : size55.card = 55`;
- `size55_seven_sperner : IsKSperner 7 size55`;
- `size55_saturated : IsSaturatedKSperner 7 size55`;
- `size55_full_certificate : size55.card = 55 ∧ IsSaturatedKSperner 7 size55`.

This is a `FORMALIZED` certificate for the explicit 55-member family on
`Fin 11`. It is now one component of the parameterized stable-value proof.

## Finite-certificate architecture

The 7-Sperner half writes the family as the union of seven explicitly checked
antichain layers and applies the generic pigeonhole theorem
`layerUnion_isKSperner`.

For saturation, every one of the `2^11 = 2048` ground subsets is assigned a
row in a frozen table.  The 55 family members use an empty row.  Each of the
other 1993 rows is a descending strict chain of exactly eight members through
that external subset after it is inserted into the family.  The rows are split
into 32 modules of 64 masks.  Every module uses kernel reduction (`decide`) to
check length, membership, strict containment, and occurrence of the inserted
set.  The main theorem proves that the 32 intervals cover all eleven-bit masks
and transports the mask result back to every `Finset (Fin 11)`.

The Python generator is not trusted: it creates candidate rows, but the Lean
proof checks every emitted row.  The generator also reproduces a semantic
table hash of
`6593d440b082ff49be9bfdd55123d981f475f8ba718f58c4ad2d471daf2c9ca7`.

## Trust audit

The forbidden token and bypass scan over Lean sources returned zero hits.
This includes `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, and
`run_tac`. `#print axioms` for both final theorems reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

An earlier experimental `native_decide` build was rejected during audit and
is not present in the final sources or proof dependencies.

## Final verification

The repository-wide command below completed all 17488 jobs:

```bash
lake build AiMathLab AiMathLab.P0054Sat7StableExact
```

The formal entry point also passed:

```bash
lake env lean Problems/P0054/formal/Main.lean
```

## Earlier finite-certificate measurements

- Kernel-reduction rebuild of all 32 blocks and the main theorem: 216.38 s.
- Cached direct check of `Problems/P0054/formal/Main.lean`: about 10 s.
- The split build peaked at a reported process footprint of about 0.85 GB;
  imported shared mappings make the raw RSS figure larger on macOS.

The repository-wide validation results are recorded in
`p0054-f1-size55-formalization-summary.md`.

## Exact sat(6) chain

Lean also accepts the following public theorems:

- `witness_blocker_large : blocker witnessLarge = witnessSmall`;
- `witness_blocker_small : blocker witnessSmall = witnessLarge`;
- `witness_total_card : witnessSmall.card + witnessLarge.card = 9`;
- `local_lower : 9 <= S.card + C.card` under the arbitrary-finite-ground
  mutual-blocker and row-size hypotheses.

The lower theorem includes the two-row, three-row, and four-row cases used in
the natural proof. Its three-row incidence count and four-row
intersection-graph classification are formalized in
`AiMathLab/P0054Sat6/LocalBounds.lean`. The concrete upper witness is
formalized in `AiMathLab/P0054Sat6.lean`.

These declarations give the local theorem `m(2,3)=9` the `FORMALIZED` label.
The downstream modules also formalize the canonical-layer lower bound, the
parameterized 30-member construction, its transport to every sufficiently
large `Fin n`, and the final theorem
`Sat6StableExact.sat_six_eq_thirty`. The explicit threshold is `3*2^30`.

The sat(6) modules contain no `sorry`, `admit`, `axiom`, `unsafe`, or
`native_decide`.

## G4.13 five-row kernel

Lean accepts `AiMathLab.P0054.G413.no_kernel_completion_of_eight` on an
arbitrary finite ground set. The theorem excludes the five-row degree-three
kernel completion used in the G4.12 `(8,8)` branch. Its supporting modules
formalize blocker involution, residual identities, private witnesses, the
small-row bounds, the five-row residual cases, and all five pair-graph
branches.

This gives the exact G4.13 local theorem the `FORMALIZED` label. At the G4.13
gate, it did not yet formalize the other G4.12 branches or the global
canonical reduction. Subsequent modules closed those dependencies. Therefore:

```text
STABLE_SATURATION_6: FORMALIZED
G413_LOCAL_THEOREM: FORMALIZED
STABLE_SATURATION_7: FORMALIZED
```
