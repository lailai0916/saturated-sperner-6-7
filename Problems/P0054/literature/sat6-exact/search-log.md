# P0054 exact sat(6) literature search log

```text
SEARCH_DATE: 2026-07-26
WORKFLOWS: MULTI_SOURCE_SEARCH_AND_CITATION_VERIFICATION
VERDICT: NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE
NOVELTY_CLAIM_ALLOWED: NO
```

## Scope

The search asked whether a public source already proves
`sat(6)=30`, rather than only the published upper bound `sat(6)<=30`.
It also rechecked every literature dependency used by the lower-bound
reduction.

## Sources and exact queries

### Crossref

Endpoint: `https://api.crossref.org/works`.

Query:

```text
query.bibliographic=saturated 6-Sperner sat(6) 30
rows=20
```

The only relevant returned work was Morrison--Noel--Scott, DOI
`10.37236/4136`. The remaining results were unrelated uses of `SAT-6`,
satisfiability, or general Sperner theory.

### OpenAlex

Endpoint: `https://api.openalex.org/works`.

Queries:

```text
search="sat(6)" "saturated Sperner"
search="saturated 6-Sperner"
```

The first query returned only Morrison--Noel--Scott. The second returned
Morrison--Noel--Scott, Martin--Veldt, the Martin--Veldt preprint, and
PatternBoost. None of the indexed records states or links to a proof of
`sat(6)=30`.

### arXiv

Endpoint: `https://export.arxiv.org/api/query`.

Query:

```text
all:"saturated 6-Sperner" OR all:"sat(6)"
```

The API returned six records. All were false positives involving the SAT-6
satellite-image data set; no combinatorics preprint was returned.

### Primary papers

The following version-of-record PDFs were searched directly:

- Morrison, Noel, and Scott, *On Saturated k-Sperner Systems*, DOI
  `10.37236/4136`;
- Martin and Veldt, *Saturation of k-Chains in the Boolean Lattice*, DOI
  `10.37236/12910`.

Morrison--Noel--Scott Proposition 20 constructs a 30-member saturated
6-Sperner system for every ground set of size at least eight. Proposition 21
proves the exact stable value only for `k<=5`. Martin--Veldt still uses the
30-member system as an upper-bound construction and does not state the reverse
inequality.

## Classification

| Record | Classification | Reason |
|---|---|---|
| Morrison--Noel--Scott 2014 | `RELEVANT_UPPER_BOUND_ONLY` | Proposition 20 proves `sat(6)<=30`; Proposition 21 stops at `k<=5` |
| Martin--Veldt 2025 | `RELEVANT_STRUCTURE_AND_UPPER_BOUND` | Proposition 14 and Lemma 15 support the lower-bound reduction; no exact `sat(6)` theorem |
| Martin--Veldt arXiv versions | `DUPLICATE_OR_EARLIER_VERSION` | Same project as the 2025 version of record |
| PatternBoost 2024 | `RELATED_NOT_EQUIVALENT` | Concerns construction search and a saturated 8-Sperner system |
| arXiv SAT-6 records | `FALSE_POSITIVE` | Satellite-image classification rather than Sperner saturation |

## Coverage limitations

- MathSciNet and zbMATH full review text were not available through an
  authenticated API.
- Exact-phrase and metadata searches can miss unindexed manuscripts, theses,
  slides, and private communications.
- No author or external field expert was contacted.
- The search says nothing about work published after 2026-07-26.

The auditable verdict is therefore
`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`. It is not a proof of novelty,
priority, or first publication.
