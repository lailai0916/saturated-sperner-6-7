# P0054 mock-review revision log

Revision date: 2026-07-26.

This log records changes made after the internal three-lens AI mock review.  It
does not convert that review into independent human peer review.

The mock review predates the exact `sat(6)=30` and `sat(7)=55` sections. It is
not a review of those proofs. Their current audit is internal only, and
external specialist review remains pending.

| Concern | Disposition | Change or remaining blocker |
|---|---|---|
| R1-M1 / R3-M1 `class-optimum-artifact-access` | OPEN | The manuscript names the required release contents, but no public immutable artifact URL or archive DOI exists yet. |
| R1-M2 `composition-source-crosswalk` | RESOLVED_IN_DRAFT | Section 4 now cites Morrison--Noel--Scott Lemma 18, states the remainder family explicitly, and gives the parameter and cardinality calculation. |
| R2-M1 `novelty-status-unconfirmed` | OPEN | The scoped audit remains a bounded negative search; P0054-C5 and P0054-C9 remain `UNKNOWN`; specialist and direct-author review are still required. |
| R2-M2 `significance-scope` | RESOLVED_BY_SCOPE | The draft targets a specialist audience, states that the leading exponent is unchanged, and makes no broad-breakthrough claim. |
| R3-M2 `nonspecialist-entry-point` | RESOLVED_IN_DRAFT | The introduction now explains that 55 counts chosen subsets and that maximality requires every omitted subset to complete an eight-term chain. |
| R3-m1 `author-metadata-placeholders` | RESOLVED_BY_AUTHOR_INPUT | The author supplied affiliation, correspondence, and ORCID metadata and explicitly confirmed no research funding and no competing interests; the manuscript and separate declaration now record them. |
| SAT6-M1 `exact-local-lower-bound` | RESOLVED_IN_MANUSCRIPT | The manuscript gives a complete arbitrary-finite-ground proof of `m(2,3)=9` and the six-point witness. |
| SAT6-M2 `formalization-scope` | RESOLVED_BY_SCOPE | Lean formalizes the local blocker theorem and witness, while the canonical stable-number transfer remains explicitly `PROVED + LITERATURE`. |
| SAT6-M3 `prior-art-status` | OPEN | Crossref, OpenAlex, arXiv, and the primary papers found no equivalent public proof in the recorded scope; novelty and priority remain `UNKNOWN`. |
| SAT7-M1 `global-lower-bound-proof` | RESOLVED_IN_MANUSCRIPT | The technical appendix proves `m(2,4)=12`; the main text derives `sat(7)>=47`. |
| SAT7-M2 `exact-value-proof` | RESOLVED_IN_MANUSCRIPT | The draft now records the exhaustive profile reduction and every 54-member branch exclusion. |
| SAT7-M3 `exact-value-formalization` | RESOLVED_BY_SCOPE | Lean formalizes the G4.13 five-row kernel, not the other G4.12 branches or global canonical reduction. |
| SAT7-M4 `exact-value-human-review` | OPEN | G4.12 has an isolated internal Referee acceptance, but no independent human specialist has reviewed the proof. |

Additional pre-review repair: the endpoint and homogeneous-atom hypotheses
needed for composition are now proved in Proposition 3.3 rather than inferred
from the template notation.

## Addendum: 2026-07-27

This addendum records work completed after the historical review table above;
it does not rewrite the review or convert it into independent human review.

The July 27, 2026 Lean gate formalized both eventual exact values as
`IsStableSaturationNumber 6 30` and `IsStableSaturationNumber 7 55`.  The full
library build completed 17,488 jobs, the independent
`Problems/P0054/formal/Main.lean` check succeeded, and `#print axioms` reported
only `propext`, `Classical.choice`, and `Quot.sound`.  The source audit found
no use of `sorry`, `admit`, an `axiom` declaration, `unsafe`, `native_decide`,
or `run_tac`.

This supersedes only the current formalization-scope descriptions in SAT6-M2
and SAT7-M3.  SAT6-M3, SAT7-M4, the artifact-release concerns,
novelty, and priority remain open.  The separate conjecture
`sat(k)=A075529(k)` is deferred and remains `UNKNOWN`.

## Addendum: 2026-07-29

The author supplied the full affiliation, postal address, correspondence
email, and ORCID metadata and confirmed that the work received no research
funding and has no competing interests.  The English and Chinese manuscripts
now contain those declarations.  A separate competing-interest Word document
and a self-contained JCTA CAS submission package were prepared and visually
checked.  The telephone number remains confined to the private submission
system and is intentionally absent from manuscript and public-artifact files.

This resolves only R3-m1.  The public GitHub release and Zenodo DOI, independent
specialist review, final novelty search, and author confirmation that the work
is not under consideration elsewhere remain outstanding.

## Addendum: 2026-07-29 prepublication confirmations

The author confirmed that the manuscript has not been published previously
and is not under consideration by another journal. The author also reported
that an external specialist review had been completed. No private report is
stored in the repository, and this statement is not represented as journal
peer review.

The final pre-submission literature audit checked Crossref, arXiv, OpenAlex,
Google Scholar, the indexed Martin--Veldt citation graph, directly relevant
full texts, and GitHub code search. It found no public equivalent of either
exact value in the recorded scope. The report is
`Problems/P0054/literature/final-prepublication-audit-2026-07-29.md`.
Novelty and priority remain `UNKNOWN` because a bounded negative search does
not prove absence from all public or nonpublic sources.

## Addendum: 2026-07-29 artifact identifiers

The curated source repository is public at
`https://github.com/lailai0916/saturated-sperner-6-7`. GitHub release `v1.0.0`
and Zenodo record `21679078` were published on 29 July 2026. The record DOI is
`10.5281/zenodo.21679078`. The GitHub archive SHA-256 and Zenodo archive MD5
match the fixed local payload. Concerns R1-M1 and R3-M1 are resolved.
