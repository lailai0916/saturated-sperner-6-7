# P0054 G4.13 scratch: the remaining three-pair graphs

```text
STATUS: PROVED_CANDIDATE
SCOPE: EIGHT_BLOCKERS_WITH_TRIANGLE_OR_K1,3_PAIR_GRAPH
RESULT: MAXIMUM_DUAL_DEGREE_AT_LEAST_4
NETWORK: MATHEMATICS_OFFLINE
```

All clutters below are finite. A blocker is an inclusion-minimal transversal.

## Setup

Let $\mathcal H$ satisfy the eight-row hypotheses of the G4.13 completion
branch:

- $|\mathcal H|=8$;
- exactly three rows are pairs;
- every other row has size at least three;
- $\mathcal K=B(\mathcal H)$ has five rows, each of size at least three;
- every point has degree at most three in both $\mathcal H$ and $\mathcal K$.

The three distinct pair rows form a simple graph with three edges. The `P4`,
`P3+K2`, and `3K2` cases were treated separately. The only remaining graph
types are a triangle and a three-leaf star.

## Triangle

Suppose the pair rows are

$$
\{a,b\},\ \{b,c\},\ \{c,a\}.
\tag{1}
$$

Every row of $\mathcal K$ meets all three pairs. Hence it contains at least
two points of $\{a,b,c\}$. Summing over the five rows gives

$$
d_{\mathcal K}(a)+d_{\mathcal K}(b)+d_{\mathcal K}(c)\ge10.
\tag{2}
$$

The degree-three hypothesis gives the opposite bound

$$
d_{\mathcal K}(a)+d_{\mathcal K}(b)+d_{\mathcal K}(c)\le9,
\tag{3}
$$

a contradiction.

## Three-leaf star

Suppose the pair rows are

$$
\{x,a\},\ \{x,b\},\ \{x,c\}.
\tag{4}
$$

These three rows exhaust the allowed $\mathcal H$-degree of $x$. Therefore
the other five rows of $\mathcal H$ avoid $x$ and have size at least three.

Delete $x$ from every row of $\mathcal K$ and minimize the resulting family:

$$
\mathcal R=\min\{K\setminus\{x\}:K\in\mathcal K\}.
\tag{5}
$$

The residual-blocker identity gives

$$
B(\mathcal R)=\{H\in\mathcal H:x\notin H\}.
\tag{6}
$$

Consequently $|B(\mathcal R)|=5$, and every row of $B(\mathcal R)$ has size
at least three. Thus

$$
\tau(\mathcal R)\ge3.
\tag{7}
$$

Every row of $\mathcal K$ initially has size at least three. Deleting $x$
can create a pair only from a row containing $x$, and
$d_{\mathcal K}(x)\le3$. Hence every row of $\mathcal R$ has size at least
two and at most three rows are pairs. Moreover $|\mathcal R|\le5$. Equation
(7) gives $|\mathcal R|\ge3$, since a transversal with private witnesses has
size at most the number of rows.

Lemma 2 of `/private/tmp/p0054_g413_residual_lemmas_v3.md` now applies to
$\mathcal R$ and gives

$$
|B(\mathcal R)|\ge6,
\tag{8}
$$

contradicting (6). Thus the star is impossible.

## Consequence

The five isomorphism types of a simple three-edge graph are:

$$
P_4,P_3+K_2,3K_2,K_3,K_{1,3}.
\tag{9}
$$

The triangle and star arguments above are arbitrary-finite proofs. Together
with the pure `P4` proof and the two endpoint-projection reductions, they
exhaust every possible graph of the three pair blockers in the eight-row
branch.

The endpoint-projection checker
`/tmp/p0054_g413_k13_projection_checker.py` independently confirms the star
exclusion over eight projection classes and 1473276 extension states. That
enumeration remains `COMPUTED` and is not a proof dependency.

The accepted G4.12 files, `claims.yaml`, and `status.md` remain unchanged.
