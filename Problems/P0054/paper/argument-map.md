# P0054 manuscript argument map

## One-sentence argument

For saturated Sperner systems in Boolean lattices, an explicit finite
canonical-reduction theorem reduces the stable lower bounds to arbitrary-
finite mutual-blocker pairs; the exact local values `m(2,3)=9`, `m(2,4)=12`,
and `m(3,3)=14`, together with the 52--54 profile exclusions and an explicit
55-member construction, give `sat(6)=30` and `sat(7)=55`, both formalized in
Lean 4 without making novelty or editorial-review claims.

## Evidence chain

1. **Finite canonical reduction:** if `|F| < 2^|X|` and
   `3*2^|F| <= |X|`, an arbitrary saturated `k`-Sperner family has a
   homogeneous atom, exactly `k` nonempty canonical layers, mutual trace
   blockers, the required row-size minima, and an exact layer-cardinality
   decomposition.
2. **Six-layer local theorem:** every arbitrary-finite-ground admissible
   `(2,3)` mutual-blocker pair has total size at least nine, and a six-point
   witness attains nine.
3. **Exact six-layer value:** canonical layers have lower bounds
   `(1,5,9,9,5,1)`, matching the published 30-member construction.
4. **Seven-layer adjacent theorem:** an arbitrary-finite-ground product bound
   `|S||C|>=32` gives `m(2,4)=12`.
5. **Seven-layer middle theorem:** `m(3,3)=14`; equality is uniquely Fano up
   to inactive points and relabelling, and no total-15 pair exists.
6. **Global lower bound:** canonical layers have lower bounds
   `(1,6,12,9,12,6,1)`, whose sum is 47.
7. **Construction:** seven displayed layers have sizes
   `(1,6,12,17,12,6,1)` and total 55.
8. **Human saturation proof:** in every layer, the listed large cores are
   exactly the inclusion-maximal subsets avoiding the listed small cores.
9. **Human layering proof:** an explicit predecessor table gives one strict
   predecessor for every member above layer zero.
10. **Refined profiles:** arbitrary-finite blocker arguments exclude totals 52
   and 53 and reduce total 54 to the Fano and sixteen-middle profiles.
11. **Exact exclusion:** the Fano adjacent splits and all middle splits
   `(5,11)`, `(6,10)`, `(7,9)`, `(8,8)`, together with their duals, are
   impossible.
12. **Exact value:** exclusion of 54 gives `sat(7)>=55`; the construction gives
    the reverse inequality, so `sat(7)=55`.
13. **General consequence:** the 28/27 small/large split yields
   `sat(5*j+2+s) <= 2^s(28^j+27^j)`.
14. **Formal verification:** Lean proves
    `IsStableSaturationNumber 6 30` and
    `IsStableSaturationNumber 7 55`.  This predicate supplies one threshold
    beyond which exact attainment and optimality hold on every `Fin n`; it is
    not evaluation of a numerical `sat` function.
15. **Final Lean gate:** the 2026-07-30 full-library revalidation completed 17,488
    jobs, `Problems/P0054/formal/Main.lean` succeeded, the final theorems report
    only `propext`, `Classical.choice`, and `Quot.sound`; the scan for
    forbidden constructs returned zero matches.
16. **Referee supplement:** the separate PDF records the arbitrary-finite
    interfaces, finite search domains, one worked five-row-kernel path,
    independent replay counts, and theorem--proof--program--Lean crosswalk.
17. **Structural certificate:** a DRAT-certified exhaustive encoding proves
    that 56 is optimal inside the seven-core common-block layered template
    class; the 55 construction therefore genuinely uses the larger core.
18. **Boundary:** novelty, priority, and journal peer review are not
    established by the mathematical or formal checks.  The conjecture
    `sat(k)=A075529(k)` is deferred outside this manuscript and remains
    `UNKNOWN`; agreement through `k=7` is not used as structural evidence.

## Evidence labels

- **PROVED:** the repository contains the arguments written out in full and
  independently checked proof certificates for their stated finite encodings.
- **FORMALIZED:** the two `IsStableSaturationNumber` declarations passed the
  Lean kernel together with the arbitrary-finite reductions and branch
  exclusions on which they depend.  For the largest finite classifications,
  these Lean declarations are the primary proof objects.
- **COMPUTED:** standalone solver searches and finite experimental outputs
  retain their recorded scopes; solver return values alone are not theorems.
- **UNKNOWN:** novelty, priority, journal peer review, and the proposed
  connection with `A075529` remain unresolved.

## Primary reader

Researchers in extremal set theory, poset saturation, and computer-assisted
combinatorics.  The manuscript leads with relevance and the numerical advance,
then separates human proofs, literature dependencies, computation, and
kernel-checked exact stable-number statements.
