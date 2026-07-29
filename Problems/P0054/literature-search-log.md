# P0054 preliminary prior-art search

Search cutoff: 2026-07-21, America/Los_Angeles.

Queries included exact combinations of:

- `"saturated 7-Sperner" 56 optimal construction homogeneous set`
- `"sat(7)" 56 saturated Sperner 2025 2026`
- `"layered" "saturated antichains" computer search Sperner`
- `"Fano plane" "saturated antichain" 56 optimal`
- `"Saturation of k-Chains" 56 computer search`
- `"saturated 7-Sperner" 55`
- `"sat(7)" 55 Sperner`
- exact-title forward citations through OpenAlex and Semantic Scholar
- arXiv API query `all:saturated AND all:Sperner`

The search located the Martin--Veldt 2025 paper, the Morrison--Noel--Scott
structural paper, and PatternBoost's 108-member 8-Sperner construction.  It did
not locate a valid published 55-member saturated 7-Sperner family or a smaller
one.  The recorded forward citations of the Martin--Veldt paper were also
checked; none supplies such a construction.

OpenAlex reported two forward citations: *Poset Saturation of Unions of
Chains* and the 2026 *Extremal Poset Theory* chapter.  Semantic Scholar also
returned PatternBoost and one induced-saturation paper.  The arXiv exact-topic
query returned the Martin--Veldt, Morrison--Noel--Scott, saturation-spectrum,
and Gerbner et al. papers.  Exact web searches for `55` found no mathematical
hit beyond the 56-member Martin--Veldt source itself.  These services can miss
unindexed or very recent work, so this remains a bounded negative search.

The arXiv history of `2402.14113` needs explicit treatment.  Versions 1 and 2
claimed a 54-member family, but version 3 withdrew it, and the final publication
acknowledges that the claimed lower value was false.  Direct reconstruction
with the current verifier finds that its layer `A2` is not saturated; in the
paper's one-based core notation, `{2,3,6}` is a counterexample.  Therefore that
withdrawn claim is not valid prior art for the present upper bound.

This is a bounded negative search, not proof of novelty.  Author contact,
MathSciNet/zbMATH review, citation-graph expansion, and expert review remain
required before using `NOVEL` wording.

Primary sources:

- <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i1p55>
- <https://arxiv.org/abs/1402.5646>
- <https://arxiv.org/abs/2411.00566>
- <https://arxiv.org/abs/2402.14113>
- <https://arxiv.org/abs/2505.23128>
- <https://doi.org/10.1007/s11083-026-09731-6>
