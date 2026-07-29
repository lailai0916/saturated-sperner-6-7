# P0054 G4.13 Lean plan and gate status v1

```text
G413_LEAN_FORMALIZED: NO
G412_EXACT_VALUE_LEAN_FORMALIZED: NO
SIZE_55_CONSTRUCTION_LEAN_FORMALIZED: YES
FORMAL_REPOSITORY_BOUNDS: 47 <= sat(7) <= 55
G412_INTERNAL_CANDIDATE: sat(7)=55
CLAIM_OR_STATUS_UPDATE_AUTHORIZED: NO
```

## Current evidence

The live P0054 worktree is on commit
`58f005e2f0bde9103acd15d37a6a22ce16308ad9`. The G4.12 exact-value files are
untracked. Neither `claims.yaml` nor `status.md` contains the exact-value
candidate.

The formal claim ledger proves the global interval:

$$
47\le\operatorname{sat}(7)\le55
$$

The internally accepted G4.12 candidate is:

$$
\operatorname{sat}(7)=55
$$

It remains outside the formal ledger.

The existing Lean entry file has 12 lines and imports only the concrete
55-member construction. Lean proves its cardinality and saturation on
`Fin 11`. It does not define the stable saturation number, exclude 54, or
formalize G4.12/G4.13.

## Formalization target

The first Lean target should be the local G4.13 theorem:

```text
No five-row degree-three kernel satisfying the locked G4.13 hypotheses
extends to an admissible eight-row mutual-blocker side.
```

This target is strictly weaker than a Lean theorem
$\operatorname{sat}(7)=55$. It isolates the new mathematics and avoids mixing
it with the remaining G4.12 computations.

## Module order

1. `ClutterBasic.lean`.
   Define finite clutters, transversals, blockers, row and point degrees,
   private rows, and minimization;
2. `BlockerInvolution.lean`.
   Prove blocker involution, minimal-transversal witnesses, and the
   point-in-blocker lemma;
3. `Residual.lean`.
   Prove both residual blocker identities and the two disjoint injections;
4. `SmallRows.lean`.
   Formalize the one-, two-, and three-blocker formulas and the exact
   three-row partition;
5. `ResidualBounds.lean`.
   Formalize the G4.9 four-row/five-row imports, residual Lemmas 1 and 2, and
   their arbitrary-finite quantifiers;
6. `FiveRowPairs.lean`.
   Formalize the loop-multigraph lemma and the exactly-three-pairs theorem;
7. `PairEndpoint.lean`.
   Formalize the repaired six-blocker lower bound and five-blocker corollary;
8. `PairGraphs/P4.lean`.
   Formalize central supports, residual involution, trace lemma, and lift;
9. `PairGraphs/P3K2.lean`.
   Formalize nine projections, the full-row fan, normal forms, endpoint
   pressure, and extension closure;
10. `PairGraphs/ThreeK2.lean` and `PairGraphs/Remaining.lean`.
    Formalize the cube classification, persistence lemma, K3 incidence count,
    and K1,3 residual contradiction;
11. `FiveRowKernel.lean`.
    Combine the kernel sizes 6, 7, and 8 with the completion lemma;
12. `G413.lean`.
    Export the local no-completion theorem and its exact statement crosswalk.

The order is acyclic and follows the natural-language dependency manifest.

## Exact-value continuation

After the local theorem passes, a Lean proof of
$\operatorname{sat}(7)=55$ still requires:

- a definition of the eventual stable saturation number;
- the global homogeneous-atom and canonical-layer reduction;
- both remaining 54-member profiles;
- the Fano adjacent splits;
- the $(5,11)$, $(6,10)$, degree-four $(8,8)$, and $(7,9)$ branches;
- verified finite certificates wherever G4.12 still uses computation;
- the connection from the existing concrete `Fin 11` construction to the
  stable upper bound.

G4.13 alone cannot close this list.

## Lean gate

Promotion requires all of the following:

```text
lake build
lake env lean Problems/P0054/formal/Main.lean
no sorry
no admit
no new axiom
no unsafe
no native_decide
no run_tac
statement crosswalk exact
#print axioms audited
two independent proof reviews
```

The expected axiom set should not exceed the existing
`propext`, `Classical.choice`, and `Quot.sound` boundary without an explicit
review.

## Gate verdict

```text
G413_NATURAL_LANGUAGE: PROVED_CANDIDATE
G413_ADVERSARIAL_REVIEW: ACCEPT_SAME_AGENT
G413_LEAN: NOT_STARTED
G412_EXACT_VALUE: PROVED_CANDIDATE_NOT_FORMAL_CLAIM
PUBLIC_OR_FORMAL_PROMOTION: BLOCKED_PENDING_INDEPENDENT_REVIEW_AND_LEAN
```

No repository file, claim file, status file, commit, or push is changed by
this plan.

