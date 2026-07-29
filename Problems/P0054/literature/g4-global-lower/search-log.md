# P0054 G4 global-lower-bound literature search log

## Execution and isolation

- `COMPUTED`: search date `2026-07-22`, timezone
  `America/Los_Angeles` (`PDT`, UTC-07:00).
- `COMPUTED`: Scout A ran read-only and online, did not read Scout B, did not
  attempt a proof, and did not write repository files.
- `COMPUTED`: Scout B ran under the same restrictions and did not read Scout
  A. After submission it independently rechecked three VOR glyph/formula
  discrepancies identified by the main Agent and issued a correction.
- `COMPUTED`: the main Agent independently read the three primary PDFs and
  recomputed the `k=7` specialization of Martin--Veldt Theorem 18.

## Primary-source retrieval

| Time (PDT) | Source/endpoint | Request | Result |
|---|---|---|---|
| 08:4x | EJC VOR | Martin--Veldt DOI `10.37236/12910` and direct PDF | `RELEVANT_PRIMARY`; 13-page VOR read; PDF SHA-256 `e5183031a356080e053ead0766373b4f62eed130e3020b72003617030d670cf2` |
| 08:4x | EJC VOR | Morrison--Noel--Scott DOI `10.37236/4136` and direct PDF | `RELEVANT_PRIMARY`; PDF SHA-256 `c85aaa9e717de586f0f166d39a6cb64d0a514ab2dc60a62fab1911c127110581` |
| 08:4x | arXiv | Gerbner et al. `arXiv:1105.4453` PDF | `RELEVANT_PRIMARY`; PDF SHA-256 `eaf3ce7f53045ff6fc8d810e7b1b469468e198510f6c4985e39c946c5790d89e` |
| 08:4x | arXiv history/API | `2402.14113`, `1402.5646`, `1105.4453`, `2505.23128` | Version histories checked; Ji et al. classified `RELATED_NOT_EQUIVALENT` |
| 08:4x | Crossref REST | `/works/10.37236/12910` and bibliographic query for `saturated 7-Sperner`, 2025--2026 | DOI metadata returned; local field extraction was incomplete, so no negative inference retained |
| 08:4x | OpenAlex REST | `/works/https://doi.org/10.37236/12910` | Work `W4408890044`; `cited_by_count=2` at query time |
| 08:4x | OpenAlex REST | `/works?filter=cites:W4408890044&per-page=50` | Two indexed forward citations: Ji--Patkós--Yue 2026 and *Extremal Poset Theory* 2026 |
| 08:4x | Semantic Scholar Graph API | paper/citation requests for DOI `10.37236/12910` | Scout A received HTTP 429; Scout B retained a three-record index response in a separate attempt; index disagreement recorded as coverage variance |

## Exact discovery queries

The two Scouts used the following exact strings, spelling variants, and
date-restricted variants across ordinary web academic search, Crossref,
OpenAlex, Semantic Scholar, arXiv, and the GitHub repositories API:

1. `"saturated 7-Sperner" lower bound`
2. `"sat(7)" "lower bound" Sperner`
3. `"sat(7)" "saturated" Sperner lower bound`
4. `"saturated 7-Sperner" 2025 OR 2026`
5. `"sat(7)" Sperner 2025 OR 2026`
6. `"canonical decomposition" "homogeneous atom" saturated Sperner`
7. `"layered saturated antichain" "k=7"`
8. `"Martin Veldt" "Lemma 15" "sat(7)"`
9. `"Martin Veldt" "Lemma 17" "k=7"`
10. `"Saturation of k-Chains in the Boolean Lattice" citations`
11. `"sat(7)" "56" saturated Sperner`
12. `"saturated 7-Sperner" "36" OR "37"`
13. `"sat(7)" "37" Sperner`
14. `"saturated k-Sperner" thesis OR dissertation`
15. `"saturated 7-Sperner" thesis OR dissertation OR GitHub`
16. `"saturated k-Sperner" 2026`
17. `"Poset Saturation of Unions of Chains" "sat(7)"`
18. `"Extremal Poset Theory" "Saturation of k-Chains"`
19. `"Saturation of k-Chains in the Boolean Lattice" GitHub code`
20. GitHub repositories API query `"saturated k-Sperner"`

## Hit classification

| Query cluster | Retained hits | Classification |
|---|---|---|
| Exact titles and DOI | Gerbner et al. 2013; MNS 2014; Martin--Veldt 2025 | `RELEVANT_PRIMARY` |
| `sat(7)` lower bound | Martin--Veldt Theorems 4 and 18 | `RELEVANT_GENERAL_BOUND`; Theorem 18 yields `sat(7)>=10` |
| `36`, `37`, stronger | No relevant indexed primary theorem located | `NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`, not global absence |
| Martin--Veldt forward citations | Ji--Patkós--Yue; PatternBoost; induced complete-bipartite-poset work; 2026 survey metadata | `RELATED_NOT_EQUIVALENT` or `METADATA_ONLY` |
| Theses/dissertations | No accessible thesis with a verified target numerical result located | `NO_RELEVANT_HIT_IN_RECORDED_SCOPE` |
| GitHub repositories API | `total_count=0` for the recorded repository-title/description query | `LIMITED_NEGATIVE`; not a code-wide absence claim |

## Scout disagreement and correction ledger

1. `COMPUTED`: Scout B initially transcribed Martin--Veldt Lemma 17 as
   `k>7`; direct VOR recheck corrected it to `k>=7`.
2. `COMPUTED`: both the main Agent and the corrected Scout checks read the
   VOR homogeneous threshold as `|H|>=2`, conflicting with older local
   source-pack text that says `>2`.
3. `COMPUTED`: Scout B initially retained the historical `sat(7)>=9`
   baseline; direct Theorem 18 specialization corrected the strongest
   checked published consequence to `sat(7)>=10`.
4. `COMPUTED`: Semantic Scholar exposed different citation coverage across
   attempts (HTTP 429 versus three returned records); no completeness claim
   is made from either response.

## Inaccessible or incomplete coverage

- `UNKNOWN`: the full text of the 2026 Cambridge survey chapter was not
  lawfully accessible in this environment.
- `UNKNOWN`: MathSciNet, zbMATH review text, Scopus, Web of Science, and a
  complete Google Scholar index were not available through auditable APIs.
- `UNKNOWN`: ordinary web search can miss unindexed preprints, theses,
  conference slides, source files, and private manuscripts.
- `UNKNOWN`: no author or external expert was contacted.
- `UNKNOWN`: the search says nothing about material published after the
  2026-07-22 cutoff.

## Frozen search verdict

`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`

The recorded scope did not locate an explicit public `sat(7)>=36`,
`sat(7)>=37`, or stronger dedicated lower bound. It did locate the published
general consequence `sat(7)>=10`. Neither result authorizes novelty wording.

