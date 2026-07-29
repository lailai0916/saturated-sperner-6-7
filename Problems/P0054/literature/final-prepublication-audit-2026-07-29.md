# Final prepublication literature and reference audit

Audit time: 2026-07-29 06:37 PDT.

## Scope and status

`SEARCHED`: This audit checks whether a public source available in the
recorded databases states or proves either exact eventual value
`sat(6)=30` or `sat(7)=55`. It also checks every bibliography entry used by
the manuscript against publisher, DOI-registry, or repository metadata.

`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`: No searched record states or
proves either exact value. This is a bounded negative search. It does not
prove novelty, priority, or absence from an unindexed or nonpublic source.

## Sources and queries

The search used the following sources in decreasing order of metadata
authority:

1. Crossref REST API, including DOI resolution and publisher metadata;
2. arXiv Atom API and the full text of directly relevant preprints;
3. OpenAlex works API, including the citation graph of Martin--Veldt;
4. Google Scholar, including the citing documents of Martin--Veldt;
5. DataCite REST API for the PatternBoost arXiv DOI;
6. GitHub code search for exact mathematical and Lean phrases.

The general web-search tool returned HTTP 404 twice. Semantic Scholar returned
HTTP 429 for both attempted queries. These failures are recorded as unavailable
channels, not as negative results.

Exact or structured query strings included:

- `"saturated 7-Sperner" 55`;
- `"sat(7)" Sperner`;
- `"saturated 6-Sperner" 30`;
- `"sat(6)" Sperner`;
- `saturated k-Sperner systems exact value`;
- `Sperner saturation 54 55`;
- arXiv `(all:Sperner AND all:saturation)`;
- Google Scholar `"sat(7)" "Sperner" OR "saturated 7-Sperner"`;
- Google Scholar `"sat(6)" "Sperner" OR "saturated 6-Sperner"`;
- OpenAlex `filter=cites:W4408890044`, where this work identifier is the
  Martin--Veldt paper;
- GitHub code search `"sat(7)" Sperner`.

## Directly relevant records

| Record | Verification | Relevance to the exact values |
|---|---|---|
| Gerbner et al., _Saturating Sperner Families_ | Publisher and Crossref metadata; DOI `10.1007/s00373-012-1195-6` | Introduces the problem and the 30-member construction used for upper bounds. It does not prove `sat(6)=30`. |
| Morrison--Noel--Scott, _On Saturated k-Sperner Systems_ | EJC article page, Crossref, and arXiv `1402.5646`; DOI `10.37236/4136` | Proves `sat(k)=2^{k-1}` for `k<=5` and gives the 30-member saturated 6-Sperner upper construction. It does not prove the matching lower bound. |
| Martin--Veldt, _Saturation of k-Chains in the Boolean Lattice_ | EJC article page, Crossref, arXiv `2402.14113v3`, and full text; DOI `10.37236/12910` | Gives a 56-member saturated 7-Sperner construction. Section 7 asks whether `sat(7)=56` or a smaller construction exists. |
| Charton--Ellenberg--Wagner--Williamson, _PatternBoost_ | DataCite, arXiv `2411.00566`, and full text | Gives a 108-member saturated 8-Sperner construction. It repeats the published 30- and 56-member upper constructions, not exact values. |
| Nick Veldt, _Induced Saturation for Various Posets_ | Iowa State repository full text, 2025 | The thesis reproduces the 56-member construction and again asks whether `sat(7)=56` or a smaller construction exists. |

Google Scholar listed four documents citing Martin--Veldt at the audit time:
PatternBoost; Liu's paper on induced saturation for complete bipartite posets;
Ji--Patkós--Yue on induced saturation of unions of chains; and Paul Bastide's
2025 thesis. Full-text or abstract checks showed that none determines the
eventual saturated 6- or 7-Sperner number. OpenAlex listed two citing works:
Ji--Patkós--Yue and the 2026 survey chapter _Extremal Poset Theory_. The survey
is relevant background but no indexed metadata or search result attributes an
exact value 30 or 55 to it.

## Bibliography verification

All eight manuscript entries resolve to the work named in the bibliography.

| Key | Status | Sources and notes |
|---|---|---|
| `gerbner2013` | `VERIFIED` | Crossref matches title, six authors, journal, volume 29, issue 5, and pages 1355--1364. Crossref's online-publication year is 2012; the cited journal issue year 2013 is correct. |
| `mns2014` | `VERIFIED` | EJC and Crossref match title, author order, volume 21, issue 3, and article P3.22. |
| `martinveldt2025` | `VERIFIED` | EJC and Crossref match title, authors, volume 32, issue 1, article P1.55, and publication date 2025-03-28. |
| `patternboost` | `VERIFIED` | DataCite and arXiv match title, four authors, year 2024, identifier 2411.00566, and DOI `10.48550/arXiv.2411.00566`. |
| `sinz2005` | `VERIFIED` | Springer and Crossref match title, author, proceedings, LNCS 3709, and pages 827--831. |
| `wetzler2014` | `VERIFIED` | Springer and Crossref match title, author order, SAT 2014, LNCS 8561, and pages 422--429. |
| `lean4` | `VERIFIED` | Springer and Crossref match title, authors, CADE-28, LNCS 12699, and pages 625--635. |
| `mathlib2020` | `VERIFIED` | ACM/Crossref metadata matches title, collective author, CPP 2020 proceedings, and pages 367--381. |

Summary: 8 verified, 0 mismatches, 0 not found, 0 requiring manual resolution.

## Submission wording authorized by this audit

The manuscript may state:

> A final pre-submission search on 29 July 2026 found no public equivalent of
> either exact value in Crossref, arXiv, OpenAlex, Google Scholar, the indexed
> citation graph, or the directly relevant full texts. This bounded negative
> search does not establish novelty or priority.

The audit does not authorize `first`, `world first`, `previously unknown in
all literature`, or any equivalent absolute priority wording.
