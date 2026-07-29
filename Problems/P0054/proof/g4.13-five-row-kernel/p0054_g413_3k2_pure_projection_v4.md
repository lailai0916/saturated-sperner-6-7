# P0054 G4.13 scratch: pure `3K2` projection

```text
STATUS: PROVED_CANDIDATE
SCOPE: EIGHT_BLOCKERS_WITH_3K2_PAIR_GRAPH
RESULT: REMOVE_THE_FIVE_CLASS_PROJECTION_AND_BOTH_SUPPORT_TABLES
NETWORK: MATHEMATICS_OFFLINE
```

All clutters below are finite. A blocker is an inclusion-minimal transversal.
This argument allows arbitrary finite ground sets and uses no endpoint or
outside-support enumeration.

## Endpoint supports

Let the three pair blockers be

$$
\{x_0,x_1\},\quad\{x_2,x_3\},\quad\{x_4,x_5\}
$$

Let $\mathcal K$ be the five-row blocker of the putative eight-row clutter.
For one pair $\{x,y\}$, write $S_x,S_y\subseteq[5]$ for the row supports of
its endpoints.

The pair is a minimal transversal, so

$$
S_x\cup S_y=[5]
$$

and both endpoints have a private row. The degree-three bound gives
$|S_x|,|S_y|\le3$. Therefore exactly one of the following occurs:

- type `D`: the supports are disjoint and have sizes two and three;
- type `I`: both supports have size three and intersect in one row.

For an endpoint $x$, put $A_x=[5]\setminus S_x$. For endpoints from different
pairs, $\{x,y\}$ is not a blocker. Since neither endpoint is a singleton
transversal, this is equivalent to

$$
A_x\cap A_y\ne\varnothing
\tag{1}
$$

for every choice of endpoints from two different pairs.

## At least one type `I` pair

For a type `I` pair with common row $w$, its two avoidance sets are disjoint
two-subsets partitioning $[5]\setminus\{w\}$.

If two type `I` pairs had different common rows, their four avoidance-set
intersections would be disjoint nonempty subsets of a three-element set.
This contradicts (1). Hence every type `I` pair has the same common row $w$.

Consider a type `D` pair. Its two avoidance sets partition all five rows and
have sizes two and three. The row $w$ cannot lie in the two-set: after deleting
$w$, that set would have only one point and could not meet both avoidance
two-sets of a type `I` pair. Thus $w$ lies in the three-set.

Delete $w$. Every endpoint pair now gives a partition of the remaining
four rows into two two-sets. Equation (1) says that any block from one
partition meets any block from another. The four cross-intersections are
disjoint and cover four rows, so every intersection has size one.

Thus the three endpoint pairs give the three pairwise orthogonal two-two
partitions of a four-element set. After permuting rows and swapping endpoints,
the four rows are the even-parity words

$$
000,\quad011,\quad101,\quad110
\tag{2}
$$

The fifth row $w$ contains both endpoints in every type `I` coordinate and
one endpoint in every type `D` coordinate. Therefore the projection is
uniquely determined by the number of type `I` pairs, which is one, two, or
three. These are the three previously computed projection classes.

The four odd-parity words define four three-endpoint blockers of the rows in
(2). Their private rows are the three Hamming neighbors in (2). The fifth row
meets each blocker through every type `I` coordinate, so all four remain
blockers after $w$ is restored.

Together with the three fixed pair blockers, the endpoint projection has
seven blockers. Each endpoint occurs in its fixed pair and in two of the four
parity blockers, so every endpoint already has degree three.

## All three pairs have type `D`

Every row now contains exactly one endpoint from each pair. Encode it by a
word in $\{0,1\}^3$, and let $M$ be the set of distinct row words.

Equation (1) says that every projection of $M$ onto two coordinates contains
all four binary pairs. Hence $|M|\ge4$. Equivalently, the missing vertex set

$$
Z=\{0,1\}^3\setminus M
$$

contains no edge of the three-dimensional cube.

There are five rows, so $|M|$ is four or five.

- If $|M|=4$, then $Z$ is an independent four-set. It is one parity class of
  the cube, $M$ is the other parity class, and the fifth row duplicates one
  word of $M$.
- If $|M|=5$, then $Z$ is an independent three-set. Any independent set of
  size at least three lies in one parity class: a mixed-parity nonadjacent
  pair consists of opposite cube vertices, whose neighborhoods exclude every
  third vertex. Thus $Z$ is three vertices of one parity class, while $M$
  contains the opposite parity class and the remaining same-parity vertex.

These are exactly the two all-`D` projection classes.

For every $z\in Z$, choose the endpoint opposite to the $z$-bit in each
coordinate. The resulting triple misses only the word $z$, so it is a
transversal. Its three Hamming neighbors belong to $M$ and are private rows,
so it is a blocker. Conversely, every blocker other than a fixed pair uses
one endpoint from each coordinate and arises this way.

When $|M|=4$, there are four triple blockers and all six endpoints have degree
three. When $|M|=5$, there are three triple blockers; one endpoint of each
pair has degree two and the other has degree three.

## Excluding the four saturated cases

The three cases with at least one type `I` pair and the duplicated all-`D`
case have seven endpoint-only blockers, with all six endpoints saturated.
The putative eighth blocker contains no endpoint.

In each parity projection, choose a full row $R$ and a two-endpoint set $Q$
that misses $R$ and meets every other projected row. The eighth blocker must
meet $R$ at some outside point $z$. Minimizing $Q\cup\{z\}$ preserves $z$ by
the private row $R$ and preserves at least one endpoint because no singleton
or pair blocker is allowed. This creates a blocker containing a saturated
endpoint, a contradiction.

For completeness, the four representatives may use the same witnesses as the
old projection reduction:

| Projection | Row mask | Two-endpoint mask |
|---|---:|---:|
| $21,21,26,38,41$ | 26 | 5 |
| $21,23,26,38,41$ | 21 | 10 |
| $21,26,31,38,41$ | 21 | 10 |
| $21,26,38,41,63$ | 21 | 10 |

The table only records four direct set-intersection checks; it is not a
classification or search.

## Excluding the asymmetric all-`D` case

Use endpoint names $A,B,C,D,E,F$. The unique asymmetric projection is

$$
\begin{aligned}
  R_0 & =\{A,C,E\} \\
  R_1 & =\{A,D,F\} \\
  R_2 & =\{B,C,F\} \\
  R_3 & =\{B,D,E\} \\
  R_4 & =\{B,D,F\}
\end{aligned}
$$

Its six blockers are

$$
\{A,B\},\{C,D\},\{E,F\},
\{A,D,F\},\{B,C,F\},\{B,D,E\}
$$

Thus $B,D,F$ already have degree three.

We first record a persistence fact. Restrict the full five-row clutter to the
six endpoints and one outside point $x$. The five endpoint rows are distinct
three-sets, so this restriction remains a clutter. If $T$ is a blocker of the
restricted clutter, every selected point has a private row. Restoring other
outside points does not change the intersection of that row with $T$.
Therefore $T$ remains a blocker in the full clutter.

Let the nonempty support of $x$ have rank at most three. If $x\notin R_4$,
the point-in-blocker lemma gives a restricted blocker containing $x$. It must
meet $R_4$ through $B,D$, or $F$, so it raises a saturated endpoint degree.
Persistence excludes this support in the full clutter.

Suppose $x\in R_4$. Up to the cyclic symmetry of $R_1,R_2,R_3$, every
support other than $\{R_4\}$ creates one of the following restricted blockers:

| Support of $x$ | Explicit blocker | Obstruction |
|---|---|---|
| $\{R_0,R_4\}$ | $\{B,D,x\}$ | saturated endpoints |
| $\{R_1,R_4\}$ | $\{B,C,x\}$ | saturated endpoint |
| $\{R_0,R_1,R_4\}$ | $\{B,x\}$ | additional pair |
| $\{R_1,R_2,R_4\}$ | $\{E,x\}$ | additional pair |

If the support is only $\{R_4\}$, the restricted family has the new blocker:

$$
\{A,C,E,x\}
$$

This saturates the remaining three endpoints. It is the unique new blocker that
avoids the already saturated set $\{B,D,F\}$.

The pointwise exclusions and persistence show that every outside point in
the full clutter must have support exactly $\{R_4\}$. If two distinct points
$x,y$ exist, both blockers

$$
\{A,C,E,x\},\qquad\{A,C,E,y\}
$$

persist in the full clutter and raise the degrees of $A,C,E$ to four. Hence
there is at most one outside point. With none there are six blockers, and
with one there are seven. The required eight-row blocker family cannot occur.

## Consequence and evidence boundary

Every endpoint-support configuration falls into the five classes above by a
pure partition and cube argument. Every class is excluded without a support
enumeration. Hence the `3K2` pair-graph branch is `PROVED_CANDIDATE`.

- `PROVED_CANDIDATE`: endpoint classification, the persistence lemma, and all
  extension exclusions.
- `COMPUTED_CROSSCHECK`: the old 125000-assignment checker and two 11-orbit
  tables agree with the proof but are no longer dependencies.
- No G4.12 protected file, claim file, or status file was modified.
- No commit, push, release, publication, or expert contact occurred.
