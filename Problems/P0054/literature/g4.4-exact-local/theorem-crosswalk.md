# P0054 G4.4 exact-local theorem crosswalk

## Exact target

`DEFINITION`: throughout this crosswalk, `H` is a finite clutter, `B(H)` is
its family of inclusion-minimal transversals, and the target hypotheses are

```text
min_{E in H}|E|>=4,
min_{T in B(H)}|T|>=2.
```

The orientation can be swapped. The candidate conclusions are:

```text
PRODUCT: |H||B(H)|>=32;
FOUR-SET: |H|=4 implies |B(H)|>=8;
EXACT: m(2,4)=12.
```

## Crosswalk

| Source/result | Exact additional hypotheses | Exact conclusion used here | Target fit | Frozen status |
|---|---|---|---|---|
| Edmonds--Fulkerson 1970 blocker involution | finite clutter | `B(B(H))=H` | exact fit for duality only | `LITERATURE`; no cardinality bound |
| Edmonds--Fulkerson Lemma B | finite clutter | subset/complement containment alternative between `H` and `B(H)` | exact fit for recognition interface | `LITERATURE`; no cardinality bound |
| Berge 1989 transversal hypergraph | finite hypergraph/clutter terminology | blocker is minimal-transversal family | exact fit for definitions | `LITERATURE`; books not fully searchable |
| Lehman 1979 width--length | `H` ideal; all nonnegative weights | weighted minimum-edge product bounded by scalar product | target lacks ideality and asks member counts | `LITERATURE`; not applicable to PRODUCT |
| ideal-blocker duality | covering polyhedron integral | ideality preserved by blocker | target lacks ideality | `LITERATURE`; not applicable |
| Bollobás 1965 set pairs | indexed pairs with `A_i∩B_j` nonempty iff `i!=j` | binomial reciprocal inequality | target has all cross pairs intersecting and no diagonal disjointness | `LITERATURE`; no direct application |
| Yolov 2018 blocker size | bounded maximum edge size and matching-minor exclusion | upper bound on blocker size | wrong hypotheses and wrong inequality direction | `LITERATURE`; not applicable |
| Stehlík 2006 τ-critical bound | connected and deletion-τ-critical | `|H|>=2 tau(H)-1` | target supplies neither extra hypothesis | `LITERATURE`; not applicable without new reduction |
| Bonomo et al. dense clutter structure | strict density/minor conditions; minimum-two members form connected graph | special structural dichotomy/minor | target permits arbitrary finite clutters | `LITERATURE`; not a classification here |
| clean tangled clutter structure | clean, tangled, `tau=2`, elementwise minimum-cover property | projective/simplex structure in strict subclass | target is broader on both sides | `LITERATURE`; not applicable globally |
| bounded-rank transversal algorithms | maximum edge size bounded | enumeration running-time bounds | target has no maximum rank or ground-set bound | `LITERATURE`; no finite proof reduction |
| exact-blocker literature | every edge/blocker pair intersects exactly once | exact blocker/anti-blocker structure | target requires only nonempty intersection | `LITERATURE`; hypothesis mismatch |

## Candidate-product audit

`UNKNOWN`: none of the frozen sources supplies

```text
|H||B(H)|>=32
```

from the two minimum-member-size hypotheses alone.

`LITERATURE`: setting all weights to one in Lehman's width--length inequality,
when its ideality hypothesis holds, relates minimum member sizes to the
ground-set size. It still does not compare the numbers of members of `H` and
`B(H)`, and it cannot be used after dropping ideality.

`LITERATURE`: applying Bollobás directly to blocker edges would reverse its
intersection pattern. A valid later proof must first manufacture indexed
disjoint diagonal pairs and verify the off-diagonal intersections.

## Four-set audit

`UNKNOWN`: none of the frozen sources supplies

```text
|H|=4, min|E|>=4, tau(H)>=2
  implies
|B(H)|>=8.
```

`DEFINITION`: `tau(H)>=2` is exactly the statement that `B(H)` has no
singleton member. It does not impose maximum edge size, uniformity,
connectedness, ideality, exact-blocker structure, or τ-criticality.

`UNKNOWN`: any reduction from a putative four-set counterexample to a
connected or τ-critical subclutter would have to preserve the four-edge
count, minimum edge size, and the relevant blocker count. No frozen source
provides that reduction.

## Exact-parameter audit

`STATUS_UNVERIFIED`: no frozen source uses the same `m(r,s)` definition or
determines the `(2,4)` instance.

`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`: both Scouts independently
searched the exact notation, blocker/transversal synonyms, product
inequalities, four-edge minimal transversals, critical clutters, books,
papers, theses/indexes, and databases without finding an equivalent public
result.

This recorded-scope conclusion must remain separate from any later proof.
It does not authorize novelty, priority, solved, best-known, or publication
language.
