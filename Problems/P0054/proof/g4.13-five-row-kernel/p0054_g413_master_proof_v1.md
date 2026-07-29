# P0054 G4.13 master proof v1

```text
STATUS: PROVED_CANDIDATE
SCOPE: G4.12_(8,8)_DEGREE_THREE_FIVE_ROW_KERNEL_BRANCH
RESULT: NO_ADMISSIBLE_EIGHT_BY_EIGHT_COMPLETION
PRIMARY_COMPUTATION: NONE
FORMAL_PROMOTION: NO
NETWORK: MATHEMATICS_OFFLINE
```

## Theorem

Work in the degree-three subbranch of G4.12 Section 10. Let $\mathcal E$ be
one eight-row side of the middle blocker pair and choose a point $x$ of
$\mathcal E$-degree three. Let $\mathcal K$ be the five rows of
$\mathcal E$ that avoid $x$, and put:

$$
\mathcal H=B(\mathcal K)
$$

Assume the inherited G4.12 conditions:

- every row of $\mathcal K$ has size at least three;
- every active point has $\mathcal K$-degree at most three;
- $|\mathcal H|\le8$;
- at most three rows of $\mathcal H$ are pairs;
- the opposite eight-row side has minimum row size three and maximum point
  degree at most three.

Then the five-row kernel has no admissible completion to the opposite
eight-row side.

This theorem allows arbitrary finite ground sets, inactive points, parallel
actual points, repeated incidence supports, and nonuniform row sizes.

## Exactly three pair blockers

The five-row pair lemma gives:

$$
|\{T\in\mathcal H:|T|=2\}|=3
$$

A singleton blocker of $\mathcal K$ would be a point of
$\mathcal K$-degree five. Hence every row of $\mathcal H$ has size at least
two, and every nonpair row has size at least three.

Blocker involution gives:

$$
B(\mathcal H)=\mathcal K
$$

Therefore:

$$
\tau(\mathcal H)ge3,
\qquad
|B(\mathcal H)|=5
$$

If $3\le|\mathcal H|\le5$, residual Lemma 2 applies to $\mathcal H$ and
gives $|B(\mathcal H)|\ge6$, a contradiction. Consequently:

$$
|\mathcal H|\in\{6,7,8\}
\tag{1}
$$

## Forced base and completion

Every pair row $P\in\mathcal H$ must acquire $x$. Otherwise it would be a
two-point row on the opposite middle side, contradicting its minimum row size
three. The three pair rows therefore use all three allowed occurrences of
$x$.

Every nonpair row of $\mathcal H$ avoids $x$ in the opposite side. Define the
forced base $\mathcal D_0$ by replacing each pair $P$ with
$P\cup\{x\}$ and retaining every nonpair row.

Any additional row $R$ avoids $x$. Every row of $\mathcal K$ must remain a
blocker, so $R$ is a transversal of $\mathcal K$. It contains some
$Q\in B(\mathcal K)=\mathcal H$.

If $Q$ is a nonpair, then $Q$ is already a row of $\mathcal D_0$. The clutter
property forbids an additional row containing it. Hence every additional row
contains one of the three pair rows of $\mathcal H$.

This is the completion lemma.

## Six or seven blockers

Assume $|\mathcal H|$ is six or seven. If the forced base already has a point
of degree at least four, the degree-three branch is impossible.

Otherwise $\Delta(\mathcal H)\le3$. The five-blocker corollary of the repaired
pair-endpoint lemma applies because:

$$
|B(\mathcal H)|=5,
\qquad
\tau(\mathcal H)\ge3,
\qquad
|\mathcal H|\ge6
$$

Every pair row has an endpoint of $\mathcal H$-degree three. At least one
additional row is needed to reach eight rows. The completion lemma makes it
contain a pair row, so it raises that endpoint degree to four. This is a
contradiction.

## Eight blockers

Assume $|\mathcal H|=8$. No completion row remains. If the forced base has a
point of degree at least four, the branch is already impossible. Otherwise:

$$
\Delta(\mathcal H)\le3,
\qquad
\Delta(\mathcal K)\le3
$$

The three pair rows form a simple graph with exactly one of five isomorphism
types:

$$
P_4,
\quad
P_3+K_2,
\quad
3K_2,
\quad
K_3,
\quad
K_{1,3}
$$

The locked pair-graph proof excludes all five cases:

- `P4` by the generalized three-row trace lemma and residual blocker lift;
- `P3+K2` by nine projections, the full-row fan, 32+5 normal forms,
  endpoint pressure, and residual closure;
- `3K2` by the partition/cube classification, row witness, and persistence
  repair;
- `K3` by the endpoint incidence sum $10>9$;
- `K1,3` by residual Lemma 2 after deleting the saturated center.

Thus the eight-blocker case is impossible.

Equation (1) exhausts all kernel sizes. This proves the theorem.

## G4.12 integration

The theorem replaces these G4.12 Section 10 dependencies in the degree-three
five-row subbranch:

```text
33,554,431 active support masks
1,890 multiplicity vectors
24 row-permutation classes
2,514 semantic extension candidates
```

Those computations remain reproducibility cross-checks. They are not primary
dependencies of this G4.13 theorem.

The theorem does not replace the other finite reductions used by the accepted
G4.12 candidate, including the separate degree-four branch and the other
middle splits. It strengthens the human-readable proof of one critical
subbranch only.

## Evidence boundary

The exact-value conclusion accepted internally by G4.12 remains:

```text
PROVED_CANDIDATE: sat(7)=55
```

G4.13 does not promote that candidate into `claims.yaml` or `status.md`. It
does not establish novelty, publication readiness, or Lean formalization.

The locked dependency list is
`/private/tmp/p0054_g413_dependency_manifest_v1.md`.

