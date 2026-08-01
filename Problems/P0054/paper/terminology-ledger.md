# P0054 terminology ledger

| Canonical term | Definition / first use | Rejected variants or scope note |
|---|---|---|
| saturated `k`-Sperner family | A `k`-Sperner family maximal under adjoining a missing ground subset | Do not use “k-saturated Sperner” except in quotations. |
| `sat(n,k)` | Minimum cardinality on an `n`-element ground set | Keep the argument order fixed. |
| `sat(k)` | Eventual stable value of `sat(n,k)` from the cited literature | The paper proves `sat(6)=30` and `sat(7)=55`; in Lean these are predicates, not evaluations of a `sat` function. |
| `IsSaturationNumberAt k n s` | Lean predicate asserting exact attainment by one saturated family of size `s` and the lower bound `s` for every saturated family on `Fin n` | Do not shorten this to a finite computation or an existence statement alone. |
| `IsStableSaturationNumber k s` | Lean predicate asserting that `IsSaturationNumberAt k n s` holds for every `n` beyond one threshold | The final theorems instantiate it at `(6,30)` and `(7,55)`. |
| blocker `B(H)` | Family of inclusion-minimal transversals of a finite family `H` | Distinguish the family from an arbitrary transversal. |
| `m(p,q)` | Minimum total size of mutual-blocker clutters with member-size minima `p` and `q`, over arbitrary finite ground sets | This paper proves `m(2,3)=9`, `m(2,4)=12`, and `m(3,3)=14`; fixed-ground computations alone do not determine this parameter. |
| finite canonical reduction | The theorem producing a homogeneous atom, exactly `k` nonempty canonical layers, mutual trace blockers, row-size bounds, and the layer cardinality identity | Its hypotheses are `|F| < 2^|X|` and `3*2^|F| <= |X|`; do not replace the second threshold by `|X| > 2^|F|`. |
| canonical layer `A_i` | The inclusion-minimal members remaining after layers `A_0,...,A_{i-1}` are successively deleted | Under the finite canonical reduction the first `k` layers are nonempty saturated antichains and cover the family. |
| core `C` | The fixed eight-element set `{1,...,8}` in the new construction | “Eight-core” is an adjective only. |
| homogeneous atom `H` | An inclusion-maximal set disjoint from `C`, with `|H|>2`, contained wholly or not at all in every family member | Maximality is proved from the fact that every core point occurs in a small member. |
| small template | A core set `S subseteq C` | Corresponds to avoiding `H`. |
| large template | `L union H` for `L subseteq C` | The “large core” is `L`, not `L union H`. |
| construction layer `A_i` | One saturated antichain in the explicit seven-layer construction | Indices run from 0 to 6; distinguish this concrete use from the general canonical-layer definition. |
| maximal small-free core | An inclusion-maximal subset of `C` containing no small core member | Central human-readable saturation certificate. |
| template class | Seven disjoint layered saturated-antichain families using sets `A` or `A union H` | The seven-core optimum is not a global lower bound. |
| `PROVED` | A fully written mathematical argument, or an independently checked proof certificate for its explicitly stated finite encoding | A compressed enumeration summary is not thereby a standalone arbitrary-finite proof; distinct from `COMPUTED`. |
| `FORMALIZED` | Accepted by the Lean kernel | The complete chain first closed on 2026-07-27 and was revalidated on 2026-07-30; it includes `sat_six_eq_thirty : IsStableSaturationNumber 6 30`, `sat_seven_eq_fifty_five : IsStableSaturationNumber 7 55`, and the exact $m(2,4)=12$ package. |
| `COMPUTED` | Reproducible finite evidence within a stated boundary | Never promoted to a universal theorem from solver output alone. |
| `UNKNOWN` | Claim not established by proof, formalization, or a sufficient evidence chain | Novelty, priority, journal peer review, and the proposed `A075529` connection remain here. |
| `SOLVED_CANDIDATE` | The exact statement has a dependency-closed proof, accepted internal referee audit, reproducible computation, and bounded prior-art audit | Independent human review is still required before `SOLVED`. |
| OEIS `A075529` | Number of distinct terminal values of star addition chains of a fixed length | This deferred conjecture is outside the present manuscript; agreement through `k=7` does not prove a general correspondence. |
