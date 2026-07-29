# P0054 terminology ledger

| Canonical term | Definition / first use | Rejected variants or scope note |
|---|---|---|
| saturated `k`-Sperner family | A `k`-Sperner family maximal under adjoining a missing ground subset | Do not use “k-saturated Sperner” except in quotations. |
| `sat(n,k)` | Minimum cardinality on an `n`-element ground set | Keep the argument order fixed. |
| `sat(k)` | Eventual stable value of `sat(n,k)` from the cited literature | The paper proves `sat(6)=30` and `sat(7)=55`; in Lean these are predicates, not evaluations of a `sat` function. |
| `IsSaturationNumberAt k n s` | Lean predicate asserting exact attainment by one saturated family of size `s` and the lower bound `s` for every saturated family on `Fin n` | Do not shorten this to a finite computation or an existence statement alone. |
| `IsStableSaturationNumber k s` | Lean predicate asserting that `IsSaturationNumberAt k n s` holds for every `n` beyond one threshold | The final theorems instantiate it at `(6,30)` and `(7,55)`. |
| blocker `B(H)` | Family of inclusion-minimal transversals of a finite family `H` | Distinguish the family from an arbitrary transversal. |
| `m(p,q)` | Minimum total size of mutual-blocker clutters with member-size minima `p` and `q` | This paper proves `m(2,3)=9` and `m(2,4)=12`. |
| core `C` | The fixed eight-element set `{1,...,8}` in the new construction | “Eight-core” is an adjective only. |
| homogeneous atom `H` | An inclusion-maximal set disjoint from `C`, with `|H|>2`, contained wholly or not at all in every family member | Maximality is proved from the fact that every core point occurs in a small member. |
| small template | A core set `S subseteq C` | Corresponds to avoiding `H`. |
| large template | `L union H` for `L subseteq C` | The “large core” is `L`, not `L union H`. |
| layer `A_i` | One saturated antichain in the seven-layer construction | Indices run from 0 to 6. |
| maximal small-free core | An inclusion-maximal subset of `C` containing no small core member | Central human-readable saturation certificate. |
| template class | Seven disjoint layered saturated-antichain families using sets `A` or `A union H` | The seven-core optimum is not a global lower bound. |
| `PROVED` | Complete mathematical proof in the repository | Distinct from finite computation. |
| `FORMALIZED` | Accepted by the Lean kernel | After the July 27, 2026 complete gate, this includes `sat_six_eq_thirty : IsStableSaturationNumber 6 30` and `sat_seven_eq_fifty_five : IsStableSaturationNumber 7 55`. |
| `COMPUTED` | Reproducible finite evidence within a stated boundary | Never promoted to a universal theorem from solver output alone. |
| `UNKNOWN` | Claim not established by proof, formalization, or a sufficient evidence chain | Novelty, priority, specialist acceptance, and the proposed `A075529` connection remain here. |
| `SOLVED_CANDIDATE` | The exact statement has a dependency-closed proof, accepted internal referee audit, reproducible computation, and bounded prior-art audit | Independent human review is still required before `SOLVED`. |
| OEIS `A075529` | Number of distinct terminal values of star addition chains of a fixed length | The conjecture `sat(k)=A075529(k)` is deferred; agreement through `k=7` does not prove a general correspondence. |
