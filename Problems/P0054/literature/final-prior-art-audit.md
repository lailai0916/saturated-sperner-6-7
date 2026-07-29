# P0054 scoped final prior-art audit

Search cutoff: 2026-07-21 (America/Los_Angeles).

## Verdict

`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`

No indexed public source located in the search below gives a valid saturated
7-Sperner family of cardinality 55 or less, the displayed eight-core family,
or the discrete bound

```text
sat(5*j + 2 + s) <= 2^s * (28^j + 27^j).
```

This is a bounded negative search, not a proof of novelty.  Claims P0054-C5
and P0054-C9 remain `UNKNOWN` pending review by a specialist and direct author
contact.  The words `first`, `novel`, and `best known` remain unauthorized.

## Sources and routing

The audit used the following source order:

1. primary papers and version histories at the Electronic Journal of
   Combinatorics and arXiv;
2. structured Crossref, OpenAlex, and Semantic Scholar records;
3. exact-phrase web searches as an incomplete last-resort index check.

The installed `nature-academic-search` fallback script could not be used: the
system has no `python` command, and its available `python3` is too old for the
script's union-type syntax.  Following the skill's failure rule, the audit
stopped retrying the script and used the direct APIs and primary pages above.

## Exact searches

Search terms included:

- `"saturated 7-Sperner" 55 OR 54 OR 56`;
- `"sat(7)" "Sperner" saturation`;
- `"55-member" "saturated" "7-Sperner"`;
- `"sat(7)" "55" combinatorics`;
- `"1,6,12,17,12,6,1" Sperner`;
- `"458H" "1346H" Sperner`;
- `"Saturation of k-Chains in the Boolean Lattice" citations`;
- `homogeneous set saturated Sperner construction`.

## Primary-source findings

1. Martin and Veldt's version of record proves a 56-member construction and
   explicitly asks whether `sat(7)=56` or a smaller construction exists.  It
   also records that an earlier lower claimed value was erroneous.
2. arXiv:2402.14113 has three versions.  Versions 1 and 2 contained the
   withdrawn 54-member claim; version 3 and the journal article do not.  The
   P0054 verifier independently rejects the withdrawn family at its third
   layer, with core set `{2,3,6}` uncovered.
3. Morrison--Noel--Scott supplies the layered-antichain and composition
   framework used to turn the displayed layers into a saturated system and to
   iterate its 28/27 split.
4. PatternBoost reports a 108-member saturated 8-Sperner construction.  It
   does not give a 55-member saturated 7-Sperner construction.

## Forward-citation audit

OpenAlex work `W4408890044` for DOI `10.37236/12910` reported two forward
citations:

- *Poset Saturation of Unions of Chains*, DOI
  `10.1007/s11083-026-09731-6`;
- *Extremal Poset Theory*, DOI `10.1017/9781009766012.003`.

Neither indexed record supplies a 55-member saturated 7-Sperner family.
Semantic Scholar reported three citing records: the first paper above,
PatternBoost, and *Induced saturation for complete bipartite posets*.  The
last two are adjacent work, not equivalent results.  Differences between the
OpenAlex and Semantic Scholar citation lists are recorded as index coverage
differences, not mathematical evidence.

## Coverage limitations

- MathSciNet and zbMATH full review text was not available through an
  authenticated API in this environment.
- Exact-phrase web search is not exhaustive and can miss unindexed source
  files, private manuscripts, conference slides, and very recent uploads.
- The Cambridge book chapter could be identified through DOI/OpenAlex but its
  complete text was not available in the current environment.
- No author or external expert was contacted in this gate.

## Required human follow-up

Before public novelty wording or journal submission:

1. ask a saturated-poset specialist to inspect the theorem statement and the
   maximal-small-free-set proof;
2. contact Martin or Veldt with the exact 55-member family and request a prior-
   art/status check;
3. repeat title, formula, and forward-citation searches immediately before
   arXiv upload or submission;
4. obtain a stable public artifact URL and archive DOI.

