# P0054 G4.4 exact-local literature search log

```text
SEARCH_DATE_LOCAL: 2026-07-22 America/Los_Angeles
SEARCH_CUTOFF_UTC: 2026-07-23
SCOUT_COUNT: 2
SCOUTS_ISOLATED: YES
SCOUTS_READ_ONLY: YES
SCOUTS_ATTEMPTED_PROOF: NO
MAIN_AGENT_NETWORK_USED: NO
NETWORK_AFTER_FREEZE: FORBIDDEN
NEGATIVE_SEARCH_CLASSIFICATION:
  NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE
STATUS_CLASSIFICATION: STATUS_UNVERIFIED
```

## 1. Scout A queries

Scout A used a general web index together with accessible pages or records
from arXiv, zbMATH, MathSciNet, Google Scholar, Crossref, DBLP, publisher
pages, author-hosted PDFs, and journal sites. Every query below was run on
2026-07-22 America/Los_Angeles.

| Database/index | Query, verbatim | Classification |
|---|---|---|
| web index | `"blocker of a clutter" cardinality theorem` | blocker duality/overview; no target cardinality theorem |
| web index | `"blocking clutters" "Lehman" theorem blocker` | ideal/minimally-nonideal literature |
| web index | `"Bollobás" "blocking clutter"` | no direct target application |
| web index | `"|H|" "B(H)" clutter inequality` | no direct product bound |
| web index | `"number of edges" "blocker" clutter` | definitions and algorithms |
| web index | `"cardinality of the blocker" clutter` | definitions and algorithms |
| web index | `"minimal transversals" "Bollobás set pairs inequality" hypergraph` | related but differently oriented set-pairs systems |
| web index | `"minimum edge size" "blocker" hypergraph inequality` | no general target theorem |
| web index | `Alfred Lehman 1965 "On the width-length inequality"` | corrected metadata to 1979 publication and correction |
| web index | `Edmonds Fulkerson 1970 blocker clutter b(b(C))` | original PDF and blocker involution |
| web index | `Bollobás 1965 set pairs inequality original paper PDF` | original metadata and modern accessible statement |
| web index | `Berge Hypergraphs blocker minimal transversals exact edition` | 1989 authoritative book record |
| web index | `"m(2,4)" blocker clutter` | no relevant mathematical result |
| web index | `"m(2,4)" "minimal transversals"` | no relevant mathematical result |
| web index | `"four edges" "minimal transversals" hypergraph at least 8` | no exact result |
| web index | `"four-member blocker" clutter` | no exact result |
| web index | `"minimum number of minimal transversals" "four" hypergraph` | no exact result |
| web index | `"number of minimal transversals" "four edges"` | no exact result |
| web index | `"minimal transversal hypergraph" "rank" "number of edges"` | maximum-rank algorithms and bounds |
| arXiv | `clutter blocker cardinality inequality` | general enumeration/minor literature |
| zbMATH | `"minimal transversals" blocker clutter cardinality` | no equivalent target theorem |
| MathSciNet | `"blocker" "clutter" "Bollobas"` | no direct target result |
| Google Scholar | `"minimum edge size" blocker clutter` | no direct target result |
| Crossref | `"blocking clutters" cardinality` | no direct target result |
| web index | `"Blocker size via matching minors" authors theorem` | Yolov 2018 and its hypotheses |
| web index/arXiv | `"Blocker size via matching minors" PDF` | accessible arXiv version |
| web index | `"Blocker size via matching minors" 2018 JCTB` | metadata correction: *Discrete Mathematics*, not JCTB |

## 2. Scout B queries

Scout B independently used a general academic web index and the Crossref
REST API, then followed results to DBLP, arXiv, publisher pages, Google
Books, author PDFs, and accessible HTML. Every query below was run on
2026-07-22 America/Los_Angeles.

| Database/index | Query, verbatim | Classification |
|---|---|---|
| academic web index | `"m(2,4)" hypergraph` | no relevant result |
| academic web index | `"m(r,s)" "hypergraph" transversal` | no relevant result |
| academic web index | `"m(r,s)" "clutter"` | no relevant result |
| academic web index | `"m(r,s)" "blocking" set systems` | no relevant result |
| Crossref REST API | `blocker clutter minimal transversal` | largely lexical noise; no parameter record |
| Crossref REST API | `transversal hypergraph minimal edge size` | general transversal literature; no parameter |
| academic web index | `"|H|" "|B(H)|" clutter` | no direct product theorem |
| academic web index | `clutter blocker "minimum cardinality" "number of edges"` | algorithms and special classes |
| academic web index | `clutter "minimum edge size" "blocker" theorem` | no general target theorem |
| academic web index | `"number of minimal transversals" hypergraph "rank"` | maximum-rank enumeration literature |
| academic web index | `"four minimal transversals" hypergraph` | no exact target classification |
| academic web index | `"four minimal transversals" "size 4" hypergraph` | no exact target classification |
| academic web index | `"minimal transversals of size at least 4" clutter` | no target theorem |

Scout B additionally searched the strict-subclass terms:

```text
tau-critical hypergraph
minimal connected tau-critical hypergraph
clean tangled clutter
dense clutter blocker
ideal minimally non-packing clutter
rank three clutter minimal covers
bounded-rank hypergraph transversal enumeration
```

The relevant hits all imposed connectedness, τ-criticality, cleanness,
tangledness, density, ideality, minor restrictions, uniformity, or bounded
maximum rank. None covered every finite clutter in the target.

## 3. Sources opened or followed

| Source | Access state | Use |
|---|---|---|
| [Edmonds--Fulkerson 1970 PDF](https://web.vu.lt/mif/s.jukna/EC_Book_2nd/Edmonds-Fulkerson.pdf) | original paper PDF opened | blocker definition, involution, partition characterization |
| [Lehman 1979 DOI](https://doi.org/10.1007/BF01582111) | metadata; primary full text inaccessible | width--length bibliographic record |
| [Király--Pap accessible PDF](https://www.keisu.t.u-tokyo.ac.jp/data/2007/METR07-04.pdf) | PDF opened | later exact restatement of Lehman inequality |
| [Bollobás 1965 DOI](https://doi.org/10.1007/BF01904851) | metadata | original set-pairs source |
| [O’Neill--Verstraëte 2021 PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v28i3p8/pdf) | PDF opened | accessible modern statement of set-pairs theorem |
| [Yolov arXiv](https://arxiv.org/abs/1606.06263) | full arXiv source | blocker-size theorem and hypotheses |
| [Berge DBLP](https://dblp.org/rec/books/daglib/0067501.html) | bibliographic record | book metadata |
| [Berge Elsevier series](https://www.sciencedirect.com/bookseries/north-holland-mathematical-library/vol/45) | publisher record | book metadata |
| [Cornuéjols Google Books](https://books.google.com/books/about/Combinatorial_Optimization.html?id=3R5DS8fhXDkC) | restricted preview | book metadata/background only |
| [Fulkerson 1972 DOI](https://doi.org/10.1016/0095-8956(72)90032-9) | abstract/metadata | anti-blocking background |
| [Stehlík author PDF](https://pagesperso.g-scop.grenoble-inp.fr/~stehlikm/papers/Ste06.pdf) | author manuscript opened | connected τ-critical theorem |
| [Bonomo et al. DOI](https://doi.org/10.1007/s10107-023-02034-3) | accessible HTML/full text | strict dense/minor subclass |
| [Abdi--Cornuéjols--Superdock arXiv](https://arxiv.org/abs/1908.10629) | full arXiv source | strict clean/tangled subclass |
| [Cochefert et al. arXiv](https://arxiv.org/abs/1510.05093) | full arXiv source | bounded-maximum-rank enumeration |
| [Eiter--Gottlob DOI](https://epubs.siam.org/doi/10.1137/S0097539793250299) | publisher record/accessible metadata | transversal-hypergraph recognition background |

## 4. Recorded negative searches

`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE` for:

1. an exact published parameter matching this definition of `m(r,s)`;
2. a classification of all finite mutual-blocker pairs with minimum member
   sizes two and four;
3. a general theorem `|H||B(H)|>=32` under those two minimum-size
   hypotheses;
4. the exact four-member implication `|B(H)|>=8`;
5. a public determination of `m(2,4)=12`.

These are query-scoped negative results. They are not proofs of absence and
do not authorize novelty, priority, “first,” “best known,” or publication
wording.

## 5. Inaccessible or incomplete coverage

- Lehman 1979 primary full text was unavailable; only metadata and a later
  accessible exact restatement were checked.
- Berge 1989 and Cornuéjols 2001 full books were not completely searchable
  through the accessible views.
- MathSciNet and zbMATH coverage was limited by accessible result views and
  snippets.
- Some theses, non-English publications, unindexed manuscripts, and alternate
  terminology may not have been retrieved.
- The external source and open/closed status of the exact local parameter
  remain `STATUS_UNVERIFIED`.
