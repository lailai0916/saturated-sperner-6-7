# P0054 G4 source-to-theorem matrix

| Source item | Exact source role | Hypotheses that must survive | Checked consequence | G4 status |
|---|---|---|---|---|
| Gerbner et al. 2013, Theorem 3(i) | General finite-`n` counting lower bound | `k<=n`; distinguishes weak and strong saturation | `2^(k/2-1)<=wsat(n,k)<=sat(n,k)` | `LITERATURE`; background only |
| Gerbner et al. 2013, stability result | Defines eventual regime | fixed `k`, sufficiently large `n` | `sat(n,k)` eventually stabilizes | `LITERATURE`; required for the last quantifier step |
| Gerbner et al. 2013, Lemma 6 | Endpoint normal-form existence | `2<=k<=n`; minimum-cardinality family can be replaced without increasing size | may choose a minimum family containing `empty` and `X` | `LITERATURE`; audit choice versus universal wording |
| MNS 2014, Definition 12 | Canonical decomposition | finite set family | iterative inclusion-minimal layers | `DEFINITION` |
| MNS 2014, Lemma 13 | Successor lemma | layered, pairwise-disjoint saturated antichains | every member of `A_i` lies strictly below some member of `A_(i+1)` | `LITERATURE`; helps prove nonempty/full-chain structure |
| MNS 2014, Lemma 14 | Forward layered union | `k` pairwise-disjoint saturated antichains, layered | saturated `k`-Sperner union | `LITERATURE`; not itself a lower bound |
| MNS 2014, Lemma 15 | Small-part layering criterion | printed source says each layer has a homogeneous set | layered iff small parts layered | `SOURCE_QUANTIFIER_CAUTION`; use MV Lemma 12 for one shared `H` |
| MNS 2014, Lemma 17 / MV 2025, Lemma 13 | Partial converse | saturated `k`-Sperner family with a homogeneous atom `H`; canonical decomposition | each canonical layer is a saturated antichain | `LITERATURE`; required for Bernoulli coverage |
| MV 2025, homogeneous definition and Lemma 6 | Atom availability | VOR threshold `|H|>=2`; `|X|>2^|F|` | existence, and uniqueness for saturated `F` | `LITERATURE`; `|F|<=55` makes `n>2^55` sufficient |
| MV 2025, Definitions 9--10 | Canonical layers and layering | exact strict-inclusion orientation | `A_0,...,A_(k-1)` source notation | `DEFINITION`; nonemptiness still needs audit |
| MV 2025, Proposition 14 | Endpoints and internal sizes | minimum-cardinality saturated family in lower-bound setup; canonical decomposition | `A_0={empty}`, `A_(k-1)={X}`; small size at least `i`; large complement size at least `k-i-1` | `LITERATURE`; minimality/selection quantifiers must be reconstructed |
| MV 2025, Lemma 15 | First/last internal layers | same minimum-family, canonical, homogeneous hypotheses | at `k=7`, `|A_1|>=6`, `|A_5|>=6` | `LITERATURE`; exact endpoint-layer input |
| MV 2025, Lemma 17 | General probabilistic layer bound | `k>=7`; `2<=i<=floor((k-1)/2)`; saturated antichain; source size bounds | exponential lower bound on `|A_i|` | `LITERATURE`; does not state `7,9,7` |
| MV 2025, Theorem 18 | Published global stable lower bound | theorem context is eventual `sat(k)` and the preceding minimum-family reduction | `sat(7)>=10` by exact specialization and integrality | `LITERATURE`; strongest checked published baseline in this pack |
| MV 2025, Section 7 question | Status question at VOR publication | none beyond paper context | asks 56 versus smaller | `LITERATURE`; never an equality/lower-bound claim |
| P0054-C7 | Existing local upper bound | verified 55-member family for all sufficiently large ground sets | `sat(7)<=55` | `PROVED`; used only for the atom-threshold selection |
| G4 Bernoulli proposal, `p=2/5` | Candidate bound for `A_2` | full coverage inequality, exact rational arithmetic, all boundary cases | proposed `|A_2|>=7` | `CONJECTURED`; Prover/Experimentalist obligation |
| G4 Bernoulli proposal, `p=1/2` | Candidate middle bound | coverage plus rigorous exclusion of equality 8 | proposed `|A_3|>=9` | `CONJECTURED`; Prover/Experimentalist obligation |
| G4 Bernoulli proposal, `p=3/5` or duality | Candidate bound for `A_4` | same source size/coverage hypotheses or a proved dual transfer | proposed `|A_4|>=7` | `CONJECTURED`; Prover/Experimentalist obligation |
| Candidate sum | Proposed global result | seven nonempty layers, no double counting, all source hypotheses, stable-`n` quantifiers | proposed `1+6+7+9+7+6+1=37` | `CONJECTURED`; no circular use of the target allowed |
| Ji--Patkós--Yue 2026 and other forward citations | Adjacent poset saturation | different parameter/poset notions | no retained `sat(7)` numerical result | `RELATED_NOT_EQUIVALENT` |
| *Extremal Poset Theory* 2026 | Survey metadata | full text unavailable | no theorem-body inference | `ACCESS_LIMITED` |

## Binding discrepancy notes

- `SOURCE_TEXT_MISMATCH_HOMOGENEOUS_THRESHOLD`: actual MV VOR is `|H|>=2`;
  older local materials saying `>2` are not binding source evidence.
- `SOURCE_QUANTIFIER_CAUTION_COMMON_H`: for a shared atom across layers, cite
  MV Lemma 12 or prove the shared quantifier; do not infer it from ambiguous
  MNS surface wording.
- `PUBLISHED_BASELINE_CORRECTION`: the historical integer baseline 9 is not
  the strongest checked published consequence after MV Theorem 18; use 10.
- `NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`: this applies only to the
  recorded search for dedicated 36/37-or-stronger results and is never a
  novelty claim.

