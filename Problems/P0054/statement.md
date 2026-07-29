# P0054 — Smaller saturated 7-Sperner systems

## Status labels

- `DEFINITION`: the search class below.
- `LITERATURE`: Martin and Veldt construct a 56-member saturated 7-Sperner family
  from seven pairwise-disjoint saturated antichains with a common homogeneous
  atom and ask whether `sat(7)=56` or a smaller construction exists.
- `PROVED`: an explicit 55-member construction exists with an eight-element
  core, proving `sat(7) <= 55`.

## Exact bounded problem

Let `C` be a finite core and let `H` be a disjoint block with `|H| > 2`.  A
template is either `A` or `A ∪ H`, where `A ⊆ C`.

Determine the minimum of

\[
  \left|\mathcal A_0 \cup \cdots \cup \mathcal A_6\right|
\]

over ordered seven-tuples satisfying all of the following:

1. every `\mathcal A_i` consists only of templates;
2. every `\mathcal A_i` is a saturated antichain in `2^{C\cup H}`;
3. the seven layers are pairwise disjoint;
4. for every `i=1,\ldots,6` and `B\in\mathcal A_i`, there is
   `A\in\mathcal A_{i-1}` with `A\subsetneq B`.

The initial decision target was whether a system of total size at most 55
exists for `|C|=4,5,6,7`.  Certificate-backed search proved that the exact
minimum for `|C|=7` is 56.  Expanding to `|C|=8` produced and independently
verified a system of size 55.  No maximality assumption is imposed on `H`.

## Why either outcome matters

- The verified eight-core construction gives the upper bound `sat(7) <= 55`
  after applying the layered construction theorem.
- A proof-certificate-backed impossibility result for the complete class gives
  a class-optimality theorem for the published 56 construction.  It does **not**
  by itself prove `sat(7)=56` globally.

## Explicitly forbidden restrictions

The search must not assume complement symmetry, the published layer sizes, the
Fano-plane pattern, or that a candidate is obtained by deleting one member of
the published family.

## Sources

- R. R. Martin and N. Veldt, *Saturation of k-Chains in the Boolean Lattice*, Electronic
  Journal of Combinatorics 32(1), 2025, P1.55.
  <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i1p55>
- The frozen P0053 source and crosswalk materials remain prior-art inputs; P0054
  does not claim novelty before a separate final audit.
