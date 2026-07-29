# P0054 G4.13 scratch: small residual lemmas

```text
STATUS: PROVED_CANDIDATE
SCOPE: THREE_AND_FOUR_ROW_RESIDUAL_BRANCHES
RESULT: REMOVE_THE_C1_THREE_ROW_AND_C2_FOUR_ROW_TABLES
NETWORK: MATHEMATICS_OFFLINE
```

## Three rows

Let $K=\set{A,B,C}$ be a three-row clutter. Assume that every row has size at
least two, at most one row has size two, and $K$ has no singleton blocker.
Then

$$
|B(K)|\ge5
\tag{1}
$$

If $B(K)$ contains a row of size three, then

$$
|B(K)|\ge6
\tag{2}
$$

The triple intersection is empty. Partition the active points into the three
private classes of sizes $p,q,r$ and the three pairwise classes of sizes
$x,y,z$. The exact blocker formula is

$$
|B(K)|=xy+xz+yz+xr+yq+zp+pqr
\tag{3}
$$

The size-three blockers are exactly the $pqr$ private triples.

Suppose first that $pqr>0$. If $pqr\ge6$, (2) follows. For $pqr<6$, the
sorted private multiplicities have one of the following forms:

$$
(1,1,1),
(1,1,2),
(1,1,3),
(1,1,4),
(1,1,5),
(1,2,2)
\tag{4}
$$

The three row-size constraints, with at most one equality at two, give the
following lower bounds in (3):

| Private multiplicities | Lower bound |
|:---:|---:|
| $(1,1,1)$ | 6 |
| $(1,1,2)$ | 6 |
| $(1,1,3)$ | 8 |
| $(1,1,4)$ | 9 |
| $(1,1,5)$ | 10 |
| $(1,2,2)$ | 8 |

For completeness, the first two tight checks are short. For $(1,1,1)$, put
$s=x+y+z$. The total row size gives $s\ge3$, and every row has size at least
two, so at least two of $x,y,z$ are positive. Hence
$xy+xz+yz\ge2$, while $xr+yq+zp=s\ge3$. For $(2,1,1)$, orient the value two
as $p=2$. If $z\ge2$, the term $zp$ is at least four. If $z=1$, at least one
of $x,y$ is positive, and its linear and quadratic contributions together
with $zp$ give at least four. If $z=0$, then $x,y\ge1$ and at least one is at
least two; the terms $xy+xr+yq$ are at least five. The other four lines are
larger versions of the same inequalities. This proves (2).

It remains that $pqr=0$. Up to permutation let $p=0$. Row incomparability
forces $x,y>0$. Formula (3) becomes

$$
|B(K)|=xy+z(x+y)+xr+yq
\tag{5}
$$

If $z=0$, incomparability gives $q,r>0$. If $x+y\ge3$, then
$xy+x+y\ge5$. If $x=y=1$, the first row is the unique allowed pair, so
$q,r\ge2$ and (5) is again at least five.

If $z>0$ and $x+y\ge3$, then $xy+z(x+y)\ge5$. If $x=y=z=1$, the first row
has size two, so the other two rows require $q,r\ge1$; (5) equals at least
five. This proves (1).

Consequently, equality in (1) has no size-three blocker. All five blockers
are pairs.

## Four large rows

Let $H$ be a four-row clutter. Assume that every row has size at least three
and $H$ has no singleton blocker. If

$$
|B(H)|\le5
\tag{6}
$$

then $B(H)$ has at least four pair rows.

If $H$ has no pair blocker, then $\tau(H)\ge3$. The accepted G4.9 four-row
lemma gives $|B(H)|\ge19$, contradicting (6). Fix a pair blocker
$\set{x,y}$.

Partition the four rows into:

- $a$ rows containing $x$ but not $y$;
- $b$ rows containing $y$ but not $x$;
- $c$ rows containing both.

Minimality gives $a,b\ge1$. Up to exchanging $x,y$, the possibilities are

$$
(a,b,c)\in\set{(1,1,2),(1,2,1),(1,3,0),(2,2,0)}
\tag{7}
$$

Delete $x,y$ from the $a$ rows and call the resulting clutter $H_x$. Define
$H_y$ analogously from the $b$ rows. Every row of these clutters has size at
least two.

For each $Q\in B(H_y)$, use $Q$ if it hits all four rows of $H$, and use
$Q\cup\set{x}$ otherwise. Private rows give an injection into $B(H)$. Its
images either avoid $x,y$ or contain $x$ but not $y$. A singleton $Q$ cannot
hit all of $H$, since that would be a singleton blocker. Thus every singleton
in $B(H_y)$ gives a pair blocker $\set{x,q}$. The symmetric statement holds
for $H_x$.

We now inspect (7).

- For $(1,1,2)$, the one-row clutters $H_x,H_y$ each supply at least two
  singleton blockers. Together with $\set{x,y}$, this gives five pair rows.
- For $(1,2,1)$, the one-row side gives two pair rows. If the two rows on the
  other side intersect, a common point gives a fourth pair row. If they are
  disjoint, their blocker has at least four rows, so the two injections and
  $\set{x,y}$ give at least seven blockers.
- For $(1,3,0)$, the one-row side again gives two pair rows. If the three-row
  side has a singleton blocker, it gives a fourth pair row. Otherwise its
  blocker has at least three rows. Indeed, one blocker would force singleton
  input rows. Two nonsingleton blockers would be disjoint, and their double
  blocker would have at least four cross-pairs rather than three rows. Thus
  the total blocker count is at least six.
- For $(2,2,0)$, consider the two two-row clutters. If exactly one has
  disjoint rows, its blocker has at least four rows; a singleton from the
  intersecting side then raises the total to at least six. If both have
  disjoint rows, both injections have size at least four. Under (6), their
  images must be the same four blockers avoiding $x,y$. They are pairs, so
  together with $\set{x,y}$ there are five pair rows. Finally, if both sides
  intersect, choose common points $u,v$. Multiple common points already give
  four pair rows. With unique common points, the four pair blockers
  $\set{x,y}$, $\set{x,v}$, $\set{y,u}$, and $\set{u,v}$ are distinct.

This proves the four-row statement.

## Consequences for the five-row pair lemma

In the $c=1$ residual branch, the three-row table is unnecessary. If
$|\mathcal T|=3$, the first lemma gives $|\mathcal R|\ge5$. Equality makes
all five rows of $\mathcal R$ pairs, contradicting its three-pair limit.

In the $c=2$ residual branch, the four-row six-vector table is unnecessary.
If $|\mathcal T|=4$, every row of $\mathcal T$ has size at least three. The
second lemma shows that $\mathcal R=B(\mathcal T)$ either has at least six
rows or at least four pair rows. Both alternatives contradict the residual
bounds.

The $c=2$ three-row case remains covered by the accepted exact three-row
formula, which gives at least seven rows in the double blocker. The same
formula removes the reverse three-row case when $|\mathcal T|=5$: five
blockers of size at least three would force $pqr=5$ and all pair terms zero,
leaving two singleton input rows.

## Remaining computed scope

This note does not replace:

- the $c=1$, four-row classification used to control the two retained triple
  rows and their intersection;
- the $c=2$, five-row branch with four or five rows in the double blocker.

Those cases remain `COMPUTED`. The G4.12 artifacts, claim files, and status
files remain unchanged.
