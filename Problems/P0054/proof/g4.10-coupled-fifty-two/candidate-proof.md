# P0054 G4.10 candidate: the equality profile of total fifty-two is impossible

```text
CURRENT_GATE: P0054_G4_10_COUPLED_TOTAL_FIFTY_TWO
CANDIDATE_CONCLUSION: sat(7) >= 53
STATUS: PROVED_CANDIDATE_PENDING_REFEREE
NETWORK: MATHEMATICS_OFFLINE
```

## 1. Statement and reduction

`PROVED_CANDIDATE` relative to the frozen G4.10 inputs: the layer profile

$$
(|A_0|,\dots,|A_6|)=(1,6,12,14,12,6,1) \tag{1.1}
$$

is impossible in the arbitrary-finite canonical decomposition.

Suppose (1.1) holds. For the middle layer, write

$$
\mathcal H=S_3, \mathcal C=C_3=B(\mathcal H).
$$

Blocker involution gives $\mathcal H=B(\mathcal C)$. Every row on both sides
has size at least three, and the frozen equality classification leaves

$$
(|\mathcal H|,|\mathcal C|)\in
\{(5,9),(6,8),(7,7),(8,6),(9,5)\}. \tag{1.2}
$$

Sections 3 and 4 exclude the four asymmetric splits. Section 5 classifies the
central split as the Fano plane. Sections 6 and 7 prove that a Fano middle
layer is incompatible with the twelve-member equality case in $A_2$.

## 2. Blocker lemmas

### Lemma 2.1: private rows

`PROVED`: if $T\in B(\mathcal D)$, then every $x\in T$ has a private row
$D_x\in\mathcal D$ such that

$$
T\cap D_x=\{x\}. \tag{2.1}
$$

Distinct points require distinct private rows. Hence

$$
|T|\le|\mathcal D|. \tag{2.2}
$$

Indeed, without (2.1), deleting $x$ would leave a transversal.

### Lemma 2.2: the three-row formula

`PROVED` from the frozen G4.9 candidate: let
$\mathcal K=\{K_1,K_2,K_3\}$ be a clutter with row sizes at least three and
$\tau(\mathcal K)\ge2$. Partition its active points into the three private
classes of sizes $p,q,r$ and the three pairwise classes of sizes $x,y,z$.
Then

$$
|B(\mathcal K)|=xy+xz+yz+xr+yq+zp+pqr. \tag{2.3}
$$

The size-three blockers are exactly the $pqr$ private triples. In particular,
$|B(\mathcal K)|\ge7$. If equality holds, at most one blocker has size three.

### Lemma 2.3: residual blockers

`PROVED`: fix a point $x$ in a clutter $\mathcal D$. Delete $x$ from every
row and keep the inclusion-minimal residual rows in $\mathcal R$. Then
$B(\mathcal R)$ is exactly the family of blockers of $\mathcal D$ that avoid
$x$.

If every residual row has size at least two, then $|B(\mathcal R)|\ge2$.
Otherwise $B(\mathcal R)=\{Q\}$, and blocker involution makes
$\mathcal R$ a family of singleton rows.

### Lemma 2.4: a three-row injection

`PROVED`: suppose $x$ belongs to some rows of $\mathcal D$, and let
$\mathcal K$ be the rows that avoid $x$. For every $T\in B(\mathcal K)$, use
$T$ if it already hits every row of $\mathcal D$, and use $T\cup\{x\}$
otherwise. Private rows in $\mathcal K$, together with a row missed by $T$ in
the second case, give an injection

$$
B(\mathcal K)\hookrightarrow B(\mathcal D). \tag{2.4}
$$

## 3. The split $(5,9)$

Exchange the two blocker sides if necessary, and assume

$$
|\mathcal H|=5, |B(\mathcal H)|=9. \tag{3.1}
$$

Every blocker has size at least three, so $\tau(\mathcal H)\ge3$.

`PROVED`: no point has incidence degree at least four. A point in four rows,
together with one point from the remaining row, gives a transversal of size
at most two. A point in all five rows gives a singleton transversal.

Suppose a point $x$ has degree three. The two rows $A,B$ avoiding $x$ are
disjoint; otherwise $x$ and a point of $A\cap B$ form a two-point
transversal. For every $a\in A$ and $b\in B$, the set $\{x,a,b\}$ is a
minimal transversal. The rows $A,B$ are private for $a,b$, and
$\tau(\mathcal H)\ge3$ makes $x$ indispensable. Thus at least

$$
|A||B|\ge9 \tag{3.2}
$$

blockers contain $x$. Lemma 2.3 gives another blocker avoiding $x$. This
contradicts (3.1).

It remains that every active point belongs to at most two rows. Represent the
points as actual loops and nonloop edges on the five row indices. Parallel
actual points remain distinct.

Choose an inclusion-minimal collection $J$ of actual points that leaves every
row degree at least three. Every point of $J$ touches a degree-three vertex;
otherwise deleting it preserves all five lower degree bounds. Let $l$ be the
number of degree-three vertices. Every other vertex has degree at least four,
and all its incidences consume degree-three incidences. Hence

$$
4(5-l)\le3l, \tag{3.3}
$$

so $l\in\{3,4,5\}$.

Every minimal edge cover of $J$ is a blocker of $\mathcal H$: it covers all
row indices, and each selected point retains a private row. The exact support
checker enumerates all multiplicities on the five loop supports and ten
nonloop supports. Every positive support touches a degree-three vertex. The
degree-three row sums are exactly three, and all other row sums are at least
four.

`COMPUTED`: the 111 minimal support covers have size distribution

$$
45,65,1 \tag{3.4}
$$

in sizes three, four, and five. For a multiplicity vector $m$, the exact
number of actual minimal edge covers is

$$
N(m)=\sum_T\prod_{s\in T}m_s, \tag{3.5}
$$

where $T$ ranges over the 111 minimal support covers. The exhaustive results
are:

| $l$ | Multiplicity vectors | Minimum $N(m)$ |
|---:|---:|---:|
| 3 | 54 | 19 |
| 4 | 2445 | 16 |
| 5 | 2698 | 15 |

All minima exceed nine. This excludes $(5,9)$ and, by exchanging sides,
$(9,5)$.

## 4. The split $(6,8)$

Assume

$$
|\mathcal H|=6, |B(\mathcal H)|=8. \tag{4.1}
$$

The frozen G4.8 high-incidence argument gives at least nine blockers when a
point belongs to at least four rows. Suppose $x$ belongs to exactly three
rows, and let $\mathcal K$ be the other three rows. Then
$\tau(\mathcal K)\ge2$, and Lemma 2.4 injects $B(\mathcal K)$ into
$B(\mathcal H)$.

If $|B(\mathcal K)|\ge9$, (4.1) fails. Consider the remaining values in
(2.3).

- If $|B(\mathcal K)|=8$, then $pqr=0$. Indeed, $pqr\ge2$ gives at least nine
  terms in (2.3). If $pqr=1$, then $p=q=r=1$. The row-size conditions give
  $x+y,x+z,y+z\ge2$. The vector $(1,1,1)$ gives seven blockers. Outside this
  vector, either one variable is zero and the other two are at least two, or
  all three are positive with sum at least four. In the two cases,
  $xy+xz+yz\ge4$. Formula (2.3) then gives at least nine blockers. Thus all
  eight blockers are pairs. Their images in (2.4) contain $x$, while
  Lemma 2.3 gives at least two blockers avoiding $x$.
- If $|B(\mathcal K)|=7$ and $pqr=0$, the same argument gives seven images
  containing $x$ and two blockers avoiding it.
- The only remaining equality vector is

  $$
  p=q=r=x=y=z=1. \tag{4.2}
  $$

  Here $B(\mathcal K)$ has six pairs and one triple. The six pair images
  contain $x$. If the triple image also contained $x$, Lemma 2.3 would give
  at least nine blockers in total. Thus (4.1) forces the triple image to avoid
  $x$ and forces exactly two blockers to avoid $x$. Let them be $T_1,T_2$.
  Lemma 2.3 gives a residual clutter
  $\mathcal R=B(\{T_1,T_2\})$ with at most six rows and no row smaller than
  two. If $T_1\cap T_2\ne\varnothing$, this blocker contains a singleton row.
  If they are disjoint, it contains at least $|T_1||T_2|\ge9$ cross-pairs.
  Both alternatives are impossible.

Therefore every point has degree at most two. Choose an inclusion-minimal
actual loop-multigraph $J$ of minimum row degree three. The frozen G4.8
matching-number zero, one, and two constructions each give at least nine
minimal edge covers. It remains that $J$ has an actual perfect matching.

Let $l$ again count its degree-three vertices. Every point touches one of
them, so

$$
4(6-l)\le3l. \tag{4.3}
$$

Thus $l\in\{4,5,6\}$. The complete 21-support checker enumerates every
allowed loop and nonloop multiplicity and retains the vectors with a
three-support perfect matching.

`COMPUTED`: the 562 minimal support covers have size distribution

$$
15,375,171,1 \tag{4.4}
$$

in sizes three through six. Formula (3.5) gives:

| $l$ | Multiplicity vectors | Minimum $N(m)$ |
|---:|---:|---:|
| 4 | 2601 | 24 |
| 5 | 31772 | 21 |
| 6 | 27325 | 15 |

The support list is complete because every member of a minimal support cover
has a distinct private vertex, so such a cover has at most six supports.
The multiplicities preserve all parallel actual points. The minimum fifteen
contradicts (4.1). This excludes $(6,8)$ and $(8,6)$.

## 5. The central split

Assume

$$
|\mathcal H|=|\mathcal C|=7. \tag{5.1}
$$

### Lemma 5.1: one side has a three-point row

`PROVED`: choose a uniformly random subset $R\subseteq U$. Exactly one of the
following events occurs:

1. $R$ contains a row of $\mathcal H$;
2. $U\setminus R$ contains a row of $\mathcal C$.

They cannot both occur because every $H\in\mathcal H$ meets every
$C\in\mathcal C$. If the first event fails, $U\setminus R$ is a transversal
of $\mathcal H$ and therefore contains a minimal transversal from
$\mathcal C$. The union bound gives

$$
1\le\sum_{H\in\mathcal H}2^{-|H|}
+\sum_{C\in\mathcal C}2^{-|C|}. \tag{5.2}
$$

If all fourteen rows had size at least four, the right side would be at most
$14/16=7/8$. Hence one side has a three-point row. Exchange the sides so that

$$
T\in\mathcal C, |T|=3. \tag{5.3}
$$

No step below assumes that $\mathcal H$ also has a three-point row.

### Lemma 5.2: point degrees are at most three

`PROVED`: a point in at least six $\mathcal H$-rows gives a transversal of
size at most two. If $x$ lies in five rows, the two remaining rows must be
disjoint. Choosing one point from each produces at least nine minimal
transversals containing $x$.

Suppose $x$ lies in four rows. Let $\mathcal K$ be the other three rows.
Lemma 2.4 applies. If $|B(\mathcal K)|\ge8$, it already contradicts (5.1).
If equality in Lemma 2.2 gives seven blockers, at most one injection image can
avoid $x$, since such an image must have size at least three. Lemma 2.3 gives
at least two blockers avoiding $x$, so at least one lies outside the seven
images. This again gives eight blockers. Therefore every active point has
$\mathcal H$-degree at most three.

### Lemma 5.3: reduction to forty-one four-row kernels

`PROVED`: the three points of $T$ cover all seven $\mathcal H$-rows. By
Lemma 5.2, one point $x\in T$ has degree exactly three. Let $\mathcal K$ be the
four $\mathcal H$-rows avoiding $x$.

We have $\tau(\mathcal K)\ge2$; otherwise $x$ and a common point of the four
rows form a two-point transversal of $\mathcal H$. Lemma 2.4 gives

$$
|B(\mathcal K)|\le7. \tag{5.4}
$$

Every row of $\mathcal K$ has size between three and seven. The upper bound
follows from Lemma 2.1 because each row belongs to
$\mathcal H=B(\mathcal C)$ and $|\mathcal C|=7$.

Encode each actual point of $\mathcal K$ by its nonempty incidence support on
the four rows. The support $15$ is absent because $\tau(\mathcal K)\ge2$.
Thus there are fourteen supports, each with multiplicity at most seven.

`COMPUTED`: `four-row-kernel.cpp` exhausts all integer multiplicity vectors,
checks row sizes, the clutter condition, and the exact weighted blocker count.
It returns:

```text
degree-feasible vectors: 7,063,970
valid clutters:          6,049,557
blocker count 5:                 6 vectors
blocker count 6:                89 vectors
blocker count 7:               475 vectors
row-permutation classes:        41 = 9 + 32
```

There are no vectors with at most four blockers. The nine low classes combine
blocker counts five and six; the other 32 classes have blocker count seven.

### Lemma 5.4: every seven-row extension is Fano

`PROVED_CANDIDATE` by the finite reduction and exhaustive certificate below:
for each of the 41 kernels, every arbitrary-finite extension back to seven
rows is covered as follows.

- Each old point has a fixed nonempty support on the four kernel rows. Its
  multiplicity is distributed over every support on the last three rows whose
  combined seven-row degree is at most three.
- Points that avoid all four kernel rows use any of the seven nonempty
  supports on the last three rows.
- One copy of support $112$ is the chosen point $x$. Additional parallel
  copies of the same support remain allowed.
- The last three row sizes range from three through seven. The program checks
  the full seven-row clutter condition and exact blocker count seven.
- The program requires a size-three blocker, as supplied by (5.3). It does
  not require a size-three row in $\mathcal H$.
- It does not reject size-one or size-two blockers. This enlarges the searched
  class beyond the theorem's hypotheses and cannot remove a counterexample.

Adding a new actual point cannot destroy an old minimal transversal: every
old selected point retains its private row. Hence pruning after the blocker
count exceeds seven is safe.

`COMPUTED`: `seven-row-extension.cpp` reads the 41 keys emitted by the first
checker and returns:

```text
kernel classes:    41
class nodes:       213,692
new-point nodes:   8,178,773
blocker prunes:    8,858,786
valid vectors:     6
non-Fano vectors:  0
```

All six labeled vectors have seven actual points, every point and row has
degree three, and every pair of rows meets in exactly one point. They are the
six labelings compatible with the fixed kernel and chosen $x$ of one Fano
plane. The frozen navigation lemma proves that its seven lines are
self-blocking. Therefore

$$
\mathcal H=\mathcal C=\mathcal L, \tag{5.5}
$$

up to relabeling, where $\mathcal L$ is the Fano line clutter.

## 6. Adjacent-layer simplification

Let

$$
\mathcal F=S_2, \mathcal G=C_2,
\mathcal H=S_3, \mathcal K=C_3.
$$

Assume both pairs are mutual blockers. `PROVED`: the four frozen conditions
between $A_2$ and $A_3$ are equivalent to:

1. every $G\in\mathcal G$ strictly contains some $K_G\in\mathcal K$;
2. $\mathcal F\cap\mathcal H=\varnothing$.

The forward direction includes item 1 directly. If
$X\in\mathcal F\cap\mathcal H$, the first frozen adjacent condition requires
either $X\subsetneq H'$ for some $H'\in\mathcal H$, contradicting the clutter
condition, or $X$ disjoint from a member of $\mathcal K$, contradicting
$X\in B(\mathcal K)$.

For the reverse direction, fix $H_0\in\mathcal H$. It meets each $K_G$ and
therefore every $G\in\mathcal G$. It contains some
$F_0\in B(\mathcal G)=\mathcal F$. The disjointness of the two row families
makes the containment strict. This is frozen condition 3.

Fix $K_0\in\mathcal K$. Every $G\in\mathcal G$ has a point outside $K_0$.
Otherwise

$$
K_G\subsetneq G\subseteq K_0
$$

contradicts the clutter condition in $\mathcal K$. Thus $U\setminus K_0$ is a
transversal of $\mathcal G$ and contains some $F_0\in\mathcal F$ disjoint
from $K_0$. This is condition 4.

Finally, if $F_0\in\mathcal F$ met every row of $\mathcal K$, it would contain
some $H_0\in B(\mathcal K)=\mathcal H$. The previous paragraph shows that
$H_0$ is also a transversal of $\mathcal G$. Minimality of $F_0$ would force
$F_0=H_0$, a contradiction. Hence $F_0$ is disjoint from some
$K\in\mathcal K$, which gives condition 1. Condition 2 was assumed.

The upper adjacent interface has the dual statement, but the lower interface
alone will exclude (5.5).

## 7. Fano cannot extend to the lower equality layer

### Lemma 7.1: four pairwise-intersecting large rows

`PROVED`: let

$$
\mathcal G=\{G_1,G_2,G_3,G_4\}
$$

be a finite clutter. Suppose every row has size at least four,
$\tau(\mathcal G)\ge2$, and every two rows intersect. Then

$$
|B(\mathcal G)|\ge9. \tag{7.1}
$$

Choose a smallest row $E=G_1$, with $n=|E|$. For $j=2,3,4$, put

$$
O_j=E\setminus G_j, R_j=G_j\setminus E.
$$

The clutter condition gives $O_j,R_j\ne\varnothing$, and minimality of $n$
gives $|R_j|\ge|O_j|$. Since there is no singleton transversal,
$O_2\cup O_3\cup O_4=E$. Pairwise intersection makes every $O_j$ a proper
subset of $E$.

For $x\in E$, define

$$
w_x=\min_{j:x\in O_j}|O_j|.
$$

The blockers that meet $E$ exactly at $x$ correspond to

$$
B(\{R_j:x\in O_j\}).
$$

Choose a smallest residual row in this family. Its size is at least $w_x$.
Apply Lemma 2.1 to that row as a member of the double blocker. This gives at
least $w_x$ such blockers. Assign each $x$ to an index attaining $w_x$, and
let $t_j$ be the number assigned to $j$. Then

$$
\sum_{x\in E}w_x
=\sum_{j=2}^4t_j|O_j|
\ge\sum_{j=2}^4t_j^2
\ge\left\lceil\frac{n^2}{3}\right\rceil. \tag{7.2}
$$

For $n\ge5$, this is at least nine. Let $n=4$ and write
$W=\sum_xw_x\ge6$. The trace family

$$
\mathcal T=\{E,E\setminus O_2,E\setminus O_3,E\setminus O_4\} \tag{7.3}
$$

has no empty row and no singleton transversal. Every minimal transversal of
$\mathcal T$ is also a blocker of $\mathcal G$ and is outside the
single-intersection classes counted by $W$.

- If $W\ge9$, (7.1) follows.
- If $W=8$, one trace blocker gives the ninth blocker.
- If $W=7$, the trace family has at least two blockers. Otherwise its minimal
  rows would include at least two singleton rows. Two omissions would then
  have size three. If the third omission has size
  $r\in\{1,2,3\}$, then

  $$
  W\ge r^2+3(4-r)\ge10,
  $$

  a contradiction.
- If $W=6$, equality in (7.2) forces the three omissions to partition $E$
  into blocks of sizes $2,1,1$. Write them as
  $\{r,s\},\{p\},\{q\}$. The five pairs

  $$
  \{r,p\},\{s,p\},\{r,q\},\{s,q\},\{p,q\}
  $$

  are distinct minimal transversals of (7.3). Thus there are at least eleven
  blockers.

This proves (7.1).

### Lemma 7.2: a seven-edge graph

`PROVED`: every simple graph $Q$ with seven vertices and seven edges that
satisfies

$$
\Delta(Q)\le3, \alpha(Q)\le3 \tag{7.4}
$$

has at least six minimal vertex covers.

Equivalently, it has at least six maximal independent sets. Suppose it has at
most five. Its fourteen nonedges must all extend to maximal independent sets.
Under $\alpha(Q)\le3$, five sets can cover all nonedges only if they are five
independent triples. Their fifteen pairs cover the fourteen nonedges, so
exactly one pair $ab$ repeats.

Let $r_v$ be the number of triples containing $v$. Counting pair incidences
at $v$ gives

$$
2r_v=
\begin{cases}
7-d(v) & v\in\{a,b\},\\
6-d(v) & v\notin\{a,b\}.
\end{cases} \tag{7.5}
$$

Condition (7.4) forces every $r_v$ to be two or three. Since
$\sum_vr_v=15$, exactly one vertex occurs three times.

Write the two triples containing the repeated pair as

$$
\{a,b,x\}, \{a,b,y\}. \tag{7.6}
$$

If the unique three-occurrence vertex is $a$, its third triple is
$\{a,p,q\}$. The remaining two triples both contain the last point and pair
$x,y,p,q$ across them. The pair $pq$ already occurs, so the pairing is
crossed. Then $\{a,x,p\}$, or its symmetric alternative, is a sixth
independent triple. The case of $b$ is identical.

If the unique vertex is neither $a$ nor $b$, the last three triples avoid
$a,b$. Their degree sequence on the remaining five points is either

$$
(1,2,2,2,2)\text{ or }(1,1,2,2,3).
$$

The sum of their three pairwise intersection sizes is respectively four or
five. Yet any two can meet in at most one point, since a second common pair
would repeat. The sum is at most three, a contradiction. Lemma 7.2 follows.

### Proposition 7.3: the lower exclusion

`PROVED`: let $X$ be the seven active Fano points and let $\mathcal L$ be its
line clutter. Put

$$
S_3=C_3=\mathcal L.
$$

Extra points in $U\setminus X$ remain allowed. Let
$\mathcal F=S_2$ and $\mathcal G=C_2$. By Section 6, every Fano line strictly
contains a row of $\mathcal F$. Such a row has size at least two and is
therefore a pair. Each pair belongs to one Fano line, so the seven lines force
seven distinct rows of $\mathcal F$. The split $(6,6)$ is impossible.

For split $(7,5)$, the seven rows of $\mathcal F$ are exactly these pairs.
They form a graph $Q$ on $X$ with one selected edge on each Fano line. Hence
$\Delta(Q)\le3$. Every minimal vertex cover is a row of
$\mathcal G=B(\mathcal F)$ and has size at least four. Thus
$\alpha(Q)\le3$. Lemma 7.2 gives $|\mathcal G|\ge6$, contradicting
$|\mathcal G|=5$. No inactive point can occur in a minimal transversal of
these seven rows.

For split $(8,4)$, every row of $\mathcal G$ strictly contains a Fano line.
The four rows are pairwise intersecting because any two Fano lines intersect.
They have size at least four, and $B(\mathcal G)=\mathcal F$ has no singleton
row. Lemma 7.1 gives $|\mathcal F|\ge9$, contradicting
$|\mathcal F|=8$.

All three allowed $A_2$ splits are impossible. Therefore the Fano middle
layer from (5.5) cannot occur in the equality profile.

## 8. Global deduction and evidence boundary

Sections 3 and 4 exclude every asymmetric split in (1.2). Section 5 reduces
the remaining split to Fano, and Proposition 7.3 excludes its lower adjacent
layer. Hence (1.1) is impossible. Together with the frozen layer lower bounds,
this gives the candidate consequence

$$
|F|\ge53,
$$

and therefore, through the frozen eventual-stability reduction,

$$
\operatorname{sat}(7)\ge53. \tag{8.1}
$$

`COMPUTED`: the finite support enumerations are proof dependencies only after
the arbitrary-finite reductions in Sections 3-5 and an independent source and
output audit. The exact commands, toolchain, hashes, and outputs are recorded
in the experiment report.

`UNKNOWN`: exact $\operatorname{sat}(7)$, novelty, priority, and a Lean
formalization of (8.1). The frozen 55-member construction still gives the
upper bound.

No change to `claims.yaml` or `status.md` is authorized by this candidate. No
publication, expert contact, push, or G4.11 work is included.
