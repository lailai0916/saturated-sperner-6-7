# P0054 G4.13 pair-endpoint Referee audit v1

```text
VERDICT: ACCEPT_AFTER_STATEMENT_REPAIR
FIRST_INVALID_STEP_IN_V1: MISSING_FIVE_BLOCKER_HYPOTHESIS_IN_THE_STATED_COROLLARY
FIRST_INVALID_STEP_IN_V2: NONE
REVIEWED_ARTIFACT: p0054_g413_pair_endpoint_lemma_v2.md
STATUS: PROVED_CANDIDATE
NETWORK: MATHEMATICS_OFFLINE
FORMAL_PROMOTION: NO
```

## Repair

Version 1 stated that every pair row has a degree-three endpoint under the
row-size, pair-budget, transversal, and degree assumptions alone. Its proof
only established the following conditional conclusion:

$$
d_{\mathcal H}(p),d_{\mathcal H}(q)\le2
\implies
|B(\mathcal H)|\ge6
$$

The intended five-row dual also satisfies $|B(\mathcal H)|=5$, but version 1
did not state that hypothesis. Version 2 repairs the statement by presenting
the lower bound first and the five-blocker conclusion as a corollary.

Version 1 also called $X\setminus\{p\}$ a pair before the three-row formula
had excluded the alternative that it was a triple. Version 2 postpones that
conclusion. The subsequent calculation proves it.

Neither repair changes any downstream application.

## Residual injection

For a pair row $\{p,q\}$ with both endpoint degrees at most two, partition
the remaining rows into $\mathcal X,\mathcal Y,\mathcal Z$. Each endpoint
side has at most one row and $|\mathcal Z|\ge3$.

The two minimized residual clutters produce disjoint blocker injections:

$$
|B(\mathcal H)|
\ge
|B(\mathcal L_p)|+|B(\mathcal L_q)|
$$

The pair row is private for the adjoined endpoint. A private minimal residual
source remains a private original row. Neither residual blocker contains a
singleton, since that would give a two-point transversal of $\mathcal H$.

Each residual has at most one singleton source. Blocker involution therefore
rules out a one-row blocker family and gives at least two blockers on each
side.

## Distribution audit

If one endpoint side is empty, the opposite residual gives at least three
blockers. A two-blocker equality on the other side would force a pair row and
a common point in at least four original rows, violating the degree-three
bound. The two injected families therefore contribute at least six blockers.

If both endpoint sides are nonempty, a two-blocker equality on one side
forces:

- the corresponding endpoint row to be a pair;
- one unique pair row in $\mathcal Z$;
- a point common to every other row of $\mathcal Z$.

The degree bound forces $|\mathcal Z|=3$. The other residual has at least
three blockers. If it has exactly three, the exact three-row formula reduces
the four-row double blocker to two pairs and two triples in the unique shape:

$$
\begin{aligned}
  A&=\{c_0,r_1\},
  &X\setminus\{p\}&=\{c_0,r_2\},\\
  Z_1&=\{s,t,r_1\},
  &Z_2&=\{s,t,r_2\}
\end{aligned}
$$

The extra blocker $\{p,q,t,r_1\}$ lies outside both residual injections.
Thus the equality branch also gives at least six blockers.

## Kernel application

Let $\mathcal K$ be the five-row kernel and
$\mathcal H=B(\mathcal K)$. Blocker involution gives:

$$
B(\mathcal H)=\mathcal K,
\qquad
|B(\mathcal H)|=5
$$

The five-row pair lemma gives exactly three pair rows in $\mathcal H$. The
kernel hypotheses give $\tau(\mathcal H)\ge3$ and the required degree bounds.

For $|\mathcal H|=6$ or $7$, the repaired corollary gives a degree-three
endpoint in every pair row. The completion lemma forces every additional row
to contain a pair row, so it raises that endpoint to degree four.

For $|\mathcal H|=8$, no completion row remains. The five possible simple
three-edge pair graphs are handled by the P4, P3+K2, 3K2, K3, and K1,3
obstructions. Each makes the inherited degree-three branch impossible.

Hence the six-, seven-, and eight-blocker branches are all structurally
closed once the pair-graph lemmas are accepted.

## Sharpness replay

The seven-row example in version 2 has exactly five blockers. The degrees of
$p,q$ are both two, while point $1$ has degree four. This confirms that the
maximum-degree hypothesis cannot be removed.

## Verdict

`FIRST_INVALID_STEP_IN_V2: NONE`.

The repaired pair-endpoint result reaches `PROVED_CANDIDATE`. Version 1 must
not appear in the final dependency manifest.

