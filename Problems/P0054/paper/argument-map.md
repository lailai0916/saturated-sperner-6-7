# P0054 manuscript argument map

## One-sentence argument

For saturated Sperner systems in Boolean lattices, we prove `sat(6)=30` from
the exact local blocker theorem `m(2,3)=9`, prove `sat(7)>=47` from
`m(2,4)=12`, exclude every 54-member canonical profile, and combine the
result with an explicit 55-member construction to obtain `sat(7)=55`; Lean 4
formalizes both eventual exact values, without establishing unconditional
novelty or replacing independent human review.

## Evidence chain

1. **Six-layer local theorem:** every arbitrary-finite-ground admissible
   `(2,3)` mutual-blocker pair has total size at least nine, and a six-point
   witness attains nine.
2. **Exact six-layer value:** canonical layers have lower bounds
   `(1,5,9,9,5,1)`, matching the published 30-member construction.
3. **Seven-layer local theorem:** an arbitrary-finite-ground product bound
   `|S||C|>=32` gives `m(2,4)=12`.
4. **Global lower bound:** canonical layers have lower bounds
   `(1,6,12,9,12,6,1)`, whose sum is 47.
5. **Construction:** seven displayed layers have sizes
   `(1,6,12,17,12,6,1)` and total 55.
6. **Human saturation proof:** in every layer, the listed large cores are
   exactly the inclusion-maximal subsets avoiding the listed small cores.
7. **Human layering proof:** an explicit predecessor table gives one strict
   predecessor for every member above layer zero.
8. **Refined profiles:** arbitrary-finite blocker arguments exclude totals 52
   and 53 and reduce total 54 to the Fano and sixteen-middle profiles.
9. **Exact exclusion:** the Fano adjacent splits and all middle splits
   `(5,11)`, `(6,10)`, `(7,9)`, `(8,8)`, together with their duals, are
   impossible.
10. **Exact value:** exclusion of 54 gives `sat(7)>=55`; the construction gives
    the reverse inequality, so `sat(7)=55`.
11. **General consequence:** the 28/27 small/large split yields
   `sat(5*j+2+s) <= 2^s(28^j+27^j)`.
12. **Formal verification:** Lean proves
    `IsStableSaturationNumber 6 30` and
    `IsStableSaturationNumber 7 55`.  This predicate supplies one threshold
    beyond which exact attainment and optimality hold on every `Fin n`; it is
    not evaluation of a numerical `sat` function.
13. **Final Lean gate:** the July 27, 2026 full-library build completed 17,488
    jobs, `Problems/P0054/formal/Main.lean` succeeded, the final theorems report
    only `propext`, `Classical.choice`, and `Quot.sound`; the scan for
    forbidden constructs returned zero matches.
14. **Structural supplement:** a DRAT-certified exhaustive encoding proves
    that 56 is optimal inside the seven-core common-block layered template
    class; the 55 construction therefore genuinely uses the larger core.
15. **Boundary:** independent human review and unconditional novelty remain
    unresolved.  The conjecture `sat(k)=A075529(k)` is deferred and remains
    `UNKNOWN`; agreement through `k=7` is not used as structural evidence.

## Evidence labels

- **PROVED:** the repository contains complete mathematical proofs of the two
  exact values and their arbitrary-finite reductions.
- **FORMALIZED:** the two `IsStableSaturationNumber` declarations passed the
  Lean kernel and the complete gate recorded above.
- **COMPUTED:** standalone solver searches and finite experimental outputs
  retain their recorded scopes; solver return values alone are not theorems.
- **UNKNOWN:** novelty, priority, independent specialist acceptance, and the
  proposed connection with `A075529` remain unresolved.

## Primary reader

Researchers in extremal set theory, poset saturation, and computer-assisted
combinatorics.  The manuscript leads with relevance and the numerical advance,
then separates human proofs, literature dependencies, computation, and
kernel-checked exact stable-number statements.
