# P0054 exact sat(6) source-to-theorem matrix

| Source item | Exact role | Hypotheses retained | Consequence used | Status |
|---|---|---|---|---|
| Gerbner et al. 2013, stability theorem | Defines the eventual stable number | fixed `k`, sufficiently large ground set | choose `n` in the stable range for `k=6` | `LITERATURE` |
| Gerbner et al. 2013, Lemma 6 | Endpoint normal form | minimum saturated family, `2<=k<=n` | choose a minimum family containing the empty and full sets | `LITERATURE` |
| Morrison--Noel--Scott 2014, Definition 12 and Lemmas 13--17 | Canonical decomposition and saturated layers | finite saturated `k`-Sperner family with the required homogeneous set | obtain six nonempty layered saturated antichains | `LITERATURE` |
| Morrison--Noel--Scott 2014, Proposition 20 | Upper bound at six layers | ground-set size at least eight | a 30-member saturated 6-Sperner family exists | `LITERATURE` |
| Morrison--Noel--Scott 2014, Proposition 21 | Historical exact-value boundary | `k<=5` | the paper does not prove the exact value at `k=6` | `LITERATURE_BOUNDARY` |
| Martin--Veldt 2025, Lemma 6 | Homogeneous-atom availability | `|X|>2^|F|` | a homogeneous atom of size at least two exists | `LITERATURE` |
| Martin--Veldt 2025, Proposition 14 | Endpoint and trace-size bounds | minimum family, canonical decomposition, homogeneous atom | endpoints are singleton layers; small members in layer `i` have size at least `i`, and complements of large traces have size at least `k-i-1` | `LITERATURE` |
| Martin--Veldt 2025, Lemma 15 | First and last internal layers | same minimum-family and homogeneous-atom setting | at `k=6`, the first and fourth layers have size at least five | `LITERATURE` |
| P0054 finite blocker involution | Local blocker interface | finite clutter | `B(B(H))=H` | `PROVED_AND_FORMALIZED` |
| P0054 local blocker theorem | Exact local lower bound | arbitrary finite ground set; mutual blockers; member-size minima two and three | every admissible pair has total size at least nine | `PROVED_AND_FORMALIZED` |
| P0054 six-point witness | Exact local upper bound | displayed five-by-four mutual-blocker pair | `m(2,3)<=9` | `PROVED_AND_FORMALIZED` |
| P0054 canonical-layer application | Global lower bound | all literature rows above plus `m(2,3)=9` | layer vector at least `(1,5,9,9,5,1)` and hence `sat(6)>=30` | `PROVED_WITH_LITERATURE_DEPENDENCIES` |

## Boundary

Lean formalizes the arbitrary-finite-ground local theorem and the explicit
witness. It does not formalize eventual stability, the homogeneous-atom
reduction, canonical layering, or the final stable-number statement.
