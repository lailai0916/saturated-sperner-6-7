# P0054 G4.4 exact-local frozen literature pack

```text
RUN_MODE: EXACT_LOCAL_PARAMETER_DISCOVERY
CURRENT_GATE: P0054_G4_4_EXACT_m_2_4
SCOUTS: TWO_ISOLATED_READ_ONLY_NETWORKED
SEARCH_DATE_LOCAL: 2026-07-22 America/Los_Angeles
SEARCH_CUTOFF_UTC: 2026-07-23
NETWORK_AFTER_FREEZE: FORBIDDEN
STATUS_CLASSIFICATION: STATUS_UNVERIFIED
NEGATIVE_SEARCH_CLASSIFICATION:
  NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE
NOVELTY_OR_PRIORITY_INFERENCE: FORBIDDEN
```

## 1. Exact object and provenance

`DEFINITION`: for an arbitrary finite ground set `U`, an admissible `(2,4)`
blocker pair consists of ordinary clutters `mathcal S,mathcal C` satisfying

```text
mathcal S=B(mathcal C),  mathcal C=B(mathcal S),
min_{S in mathcal S}|S|>=2,
min_{C in mathcal C}|C|>=4.
```

`DEFINITION`: the repository-local parameter is

```text
m(2,4)=min(|mathcal S|+|mathcal C|)
```

over all such pairs and finite ground sets.

`PROVED` in the frozen repository inputs:

```text
9<=m(2,4)<=12.
```

The upper endpoint is attained by the eight edges of two vertex-disjoint
four-cycles and their four-member blocker.

`STATUS_UNVERIFIED`: the exact local problem is derived inside P0054 from the
accepted G4.2 mutual-blocker layer interface and the G4.3 local theorem. The
two Scouts did not identify an external original problem statement, author,
date, or standard problem identifier for this exact parameter.

`STATUS_UNVERIFIED`: neither Scout found evidence that `m(r,s)` is a standard
published notation for this parameter. No absence, novelty, or priority
claim follows.

## 2. Frozen primary and authoritative sources

### 2.1 Edmonds--Fulkerson blocker duality

`LITERATURE`: Jack Edmonds and D. R. Fulkerson, “Bottleneck Extrema,”
*Journal of Combinatorial Theory* **8** (1970), 299--306.

- Original-source snapshot accessed by Scout A:
  [PDF](https://web.vu.lt/mif/s.jukna/EC_Book_2nd/Edmonds-Fulkerson.pdf).
- On p. 301 the blocker is defined as the minimal subsets meeting every
  member of a finite clutter.
- The paper states the involution `b(b(H))=H` for a clutter.
- Lemma B gives a partition-style characterization: for every subset of the
  finite ground set, either it contains a member of the clutter or its
  complement contains a member of the blocker, but not both.

`LITERATURE`: these results apply to arbitrary finite clutters and justify
the standard blocker involution and its equivalent containment interface.
They give no lower bound on `|H||B(H)|` or `|H|+|B(H)|`.

### 2.2 Berge and Cornuéjols terminology

`LITERATURE`: Claude Berge, *Hypergraphs: Combinatorics of Finite Sets*,
North-Holland Mathematical Library 45, 1989, ISBN 978-0-444-87489-4.
Scout B verified the authoritative
[DBLP record](https://dblp.org/rec/books/daglib/0067501.html) and
[Elsevier series record](https://www.sciencedirect.com/bookseries/north-holland-mathematical-library/vol/45).

`LITERATURE`: Gérard Cornuéjols, *Combinatorial Optimization: Packing and
Covering*, SIAM, 2001. Scout B accessed a restricted
[Google Books record](https://books.google.com/books/about/Combinatorial_Optimization.html?id=3R5DS8fhXDkC).

`STATUS_UNVERIFIED`: neither restricted book view was sufficient to locate a
statement about the exact `(2,4)` parameter or the candidate product
inequality. These books are frozen only as terminology/background sources.

### 2.3 Lehman width--length inequality

`LITERATURE`: A. Lehman, “On the width-length inequality,”
*Mathematical Programming* **16** (1979), 245--259,
[DOI 10.1007/BF01582111](https://doi.org/10.1007/BF01582111), with a
correction in volume 17. The primary full text was not openly accessible to
either Scout. Scout A cross-checked the bibliographic record and the exact
displayed inequality through an accessible Király--Pap paper:
[PDF](https://www.keisu.t.u-tokyo.ac.jp/data/2007/METR07-04.pdf).

`LITERATURE`: the width--length characterization requires the clutter to be
ideal. In the accessible restatement, for all nonnegative weight vectors
`w,l`,

```text
min_{E in C} w(E) * min_{B in b(C)} l(B) <= l^T w.
```

`LITERATURE`: this theorem is not applicable to the frozen target as a
cardinality inequality. The target has no ideality hypothesis, and the
conclusion concerns weights on the ground set rather than the numbers of
clutter and blocker members.

### 2.4 Bollobás set-pairs inequality

`LITERATURE`: Béla Bollobás, “On generalized graphs,”
*Acta Mathematica Academiae Scientiarum Hungaricae* **16** (1965),
447--452, [DOI 10.1007/BF01904851](https://doi.org/10.1007/BF01904851).
Scout A verified the original metadata and an accessible modern statement in
O’Neill--Verstraëte 2021:
[PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v28i3p8/pdf).

`LITERATURE`: the classical set-pairs theorem assumes indexed pairs
`(A_i,B_i)` with

```text
A_i intersects B_j iff i != j
```

and concludes the standard binomial reciprocal inequality.

`LITERATURE`: the theorem does not apply directly to the mutual-blocker pair.
The frozen blocker interface has every cross pair intersecting and supplies
no distinguished diagonal of disjoint pairs. Any later use must construct
and verify a separate indexed set-pair system satisfying the exact
if-and-only-if hypothesis.

### 2.5 Blocker size via matching minors

`LITERATURE`: Nikola Yolov, “Blocker size via matching minors,”
*Discrete Mathematics* **341** (2018), 2237--2242,
[arXiv:1606.06263](https://arxiv.org/abs/1606.06263),
[DOI 10.1016/j.disc.2018.04.004](https://doi.org/10.1016/j.disc.2018.04.004).

`LITERATURE`: the main bound concerns an upper bound on blocker size when the
maximum edge size is bounded and an additional matching-minor exclusion
holds.

`LITERATURE`: this result cannot supply the target lower bound. The frozen
problem bounds minimum member sizes, has no maximum-rank or matching-minor
hypothesis, and asks for a lower rather than an upper blocker-count bound.

### 2.6 Strict subclasses

`LITERATURE`: Matej Stehlík, “Minimal Connected τ-Critical Hypergraphs,”
*Graphs and Combinatorics* **22** (2006), 421--426,
[DOI 10.1007/S00373-006-0656-1](https://doi.org/10.1007/S00373-006-0656-1),
[author PDF](https://pagesperso.g-scop.grenoble-inp.fr/~stehlikm/papers/Ste06.pdf).
For connected τ-critical hypergraphs, the paper gives the lower bound
`|H|>=2 tau(H)-1`.

`LITERATURE`: this does not apply to the target without a proof that the
chosen side is connected and deletion of every edge strictly decreases its
transversal number. Neither property is part of the frozen statement.

`LITERATURE`: F. Bonomo, G. Durán, M. Marenco, and J. Stein,
“Intersecting and dense restrictions of clutters in polynomial time,”
*Mathematical Programming*,
[DOI 10.1007/s10107-023-02034-3](https://doi.org/10.1007/s10107-023-02034-3).
The accessible full text defines blockers and records blocker involution; its
special structure theorem assumes, among other conditions, that minimum
members are exactly two and form a connected graph.

`LITERATURE`: these dense/minor hypotheses are absent from the target, which
allows minimum member size strictly greater than two and disconnected
families. The theorem is not a classification of admissible `(2,4)` pairs.

`LITERATURE`: Ahmad Abdi, Gérard Cornuéjols, and Matt Superdock, “Clean
tangled clutters, simplices, and projective geometries,”
[arXiv:1908.10629](https://arxiv.org/abs/1908.10629), studies clean tangled
clutters, a strict subclass with transversal number two and additional
elementwise cover conditions.

`LITERATURE`: this strict subclass does not cover all admissible pairs and
does not yield the target product inequality.

### 2.7 Enumeration algorithms and exact blockers

`LITERATURE`: Cochefert, Couturier, Gaspers, and Kratsch, “Faster algorithms
to enumerate hypergraph transversals,”
[arXiv:1510.05093](https://arxiv.org/abs/1510.05093), treats
hypergraphs with bounded maximum edge size.

`LITERATURE`: this algorithmic result does not provide an arbitrary-`U`
finite reduction for the target, which has no maximum edge-size bound.

`LITERATURE`: Boros et al., “On exact blockers and anti-blockers,
Δ-conjecture, and related problems,” *Discrete Applied Mathematics* (2011),
uses “exact blocker” for the stronger property that every edge and every
minimal transversal intersect in exactly one point.

`LITERATURE`: the exact-blocker hypothesis is not present here. The target
requires only nonempty cross-intersection, so exact-blocker conclusions
cannot be imported without a new proof.

`LITERATURE`: D. R. Fulkerson, “Anti-blocking polyhedra,”
*Journal of Combinatorial Theory, Series B* **12** (1972), 50--71,
[DOI 10.1016/0095-8956(72)90032-9](https://doi.org/10.1016/0095-8956(72)90032-9),
provides polyhedral blocking/anti-blocking background. It does not state the
finite clutter edge-count product sought here.

## 3. Frozen theorem-status conclusions

`UNKNOWN`: no checked source establishes, under exactly the frozen
arbitrary-finite-clutter hypotheses,

```text
|mathcal S||mathcal C|>=32.
```

The candidate product inequality remains `CONJECTURED`, not `LITERATURE`.

`UNKNOWN`: no checked source establishes the proposed four-set theorem

```text
|mathcal C|=4,
min_{C in mathcal C}|C|>=4,
B(mathcal C) has no singleton
  implies
|B(mathcal C)|>=8.
```

`STATUS_UNVERIFIED`: no checked source determines `m(2,4)` under this exact
definition or classifies all clutters whose own and dual transversal numbers
are at least two and four.

`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`: the two independent searches
found no public theorem equivalent to the exact target, product inequality,
or four-set blocker lemma within the recorded databases, queries, accessible
papers, books, and metadata.

This is a bounded negative-search label. It does not mean no such result
exists, that this gate is the first solution, or that any later proof is
novel.

## 4. Terminology crosswalk

`DEFINITION`: for a finite clutter `H`,

```text
min_{T in B(H)}|T| = tau(H).
```

Thus the target can equivalently be written as a clutter `C` with

```text
tau(C)>=2, tau(B(C))>=4,
```

minimizing `|C|+|B(C)|`, with orientation swapped as needed.

`DEFINITION`: in most hypergraph algorithm literature, rank means maximum
edge size. The target instead imposes lower bounds on member sizes. A
rank-four theorem therefore cannot be substituted for “every member has
size at least four.”

`DEFINITION`: a τ-critical hypothesis means deletion of each edge decreases
the transversal number. It is not implied merely by being a clutter or by
mutual-blocker duality.

`DEFINITION`: “blocking clutter theorem” may refer to ideal or minimally
nonideal polyhedral structure. Those additional properties are not present
in the target.

## 5. Access and coverage gaps

- Lehman 1979: primary full text not openly accessible; the exact displayed
  inequality was cross-checked only through an accessible later paper.
- Berge 1989 and Cornuéjols 2001: bibliographic records and restricted
  previews were accessible, but no full-text search of the entire books was
  available.
- MathSciNet/zbMATH/Google Scholar results were limited to the Scouts'
  accessible indexes and snippets; absence from those results is not a
  global absence result.
- Search terminology is not canonical. Unindexed theses, non-English
  sources, or results stated through another parameter may have been missed.
- The external open/closed status and original source of the exact parameter
  remain `STATUS_UNVERIFIED`.

## 6. Permitted use after freeze

The later proof phase may use the finite-clutter blocker definitions and
involution as `LITERATURE`. It may explore Bollobás, Lehman, critical-clutter,
matching/minor, or incidence methods only after re-proving every hypothesis
needed for the target.

No negative search result, inaccessible source, theorem from a strict
subclass, or finite experiment may be upgraded into the target theorem,
novelty, priority, or publication wording.
