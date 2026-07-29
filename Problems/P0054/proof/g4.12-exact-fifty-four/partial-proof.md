# P0054 G4.12 candidate: the exact value is fifty-five

```text
CURRENT_GATE: P0054_G4_12_EXACT_FIFTY_FOUR
STATUS: PROVED_CANDIDATE_PENDING_REFEREE
CANDIDATE_RESULT: EVERY_FIFTY_FOUR_MEMBER_PROFILE_IMPOSSIBLE
CANDIDATE_CONCLUSION: sat(7) = 55
NETWORK: MATHEMATICS_OFFLINE
```

## 1. Scope

`PROVED_CANDIDATE` relative to the frozen G4.12 inputs: the profile

$$
P_{\mathrm F}=(1,6,13,14,13,6,1) \tag{1.1}
$$

is impossible in the arbitrary-finite canonical decomposition.

`PROVED_CANDIDATE`: every possible middle split in the remaining profile

$$
P_{16}=(1,6,12,16,12,6,1) \tag{1.2}
$$

is impossible. Every sixteen-member middle pair has a three-point row. The
splits $(5,11)$, $(6,10)$, $(7,9)$, and $(8,8)$, together with their blocker
duals, are all excluded.

Thus no fifty-four-member family survives the frozen canonical reduction.
Combined with the frozen 55-member construction, the candidate conclusion is

$$
\operatorname{sat}(7)=55 \tag{1.3}
$$

This is a dependency-closed candidate pending an isolated Referee. It is not
yet a claim/status update or a novelty statement.

All families below are finite clutters on one arbitrary finite ground set.
Blockers are inclusion-minimal transversals. Inactive points, parallel actual
points, repeated incidence patterns, and nonuniform rows remain allowed.

## 2. Fano setup

Let $X$ be the seven active Fano points and let $\mathcal L$ be the Fano line
clutter. In the Fano profile,

$$
\mathcal H=\mathcal K=\mathcal L
$$

For the lower adjacent pair, put $\mathcal F=S_2$ and $\mathcal G=C_2$.
The frozen adjacent interface says that every Fano line strictly contains a
row of $\mathcal F$. Such a row has size at least two and is therefore a pair.
Distinct lines require distinct pairs because every pair of Fano points lies
on exactly one line.

The three possible lower splits are

$$
(|\mathcal F|,|\mathcal G|)\in\{(7,6),(8,5),(9,4)\} \tag{2.1}
$$

The upper splits are their exact frozen duals. It is therefore enough to
exclude (2.1).

## 3. The split $(7,6)$

The seven rows of $\mathcal F$ are exactly one selected pair from each Fano
line. They form a simple seven-edge graph $Q$ on $X$, and

$$
\mathcal G=B(E(Q)) \tag{3.1}
$$

Points outside $X$ occur in no row of $\mathcal F$ and therefore cannot occur
in a minimal transversal. This is an arbitrary-finite reduction to the
$3^7=2187$ choices of one of the three pairs on every Fano line.

The strict C++ enumerator and the independent Python implementation both
recompute all minimal vertex covers. Among the $1011$ choices for which every
minimal cover has size at least four, the blocker-count distribution is

$$
7:24,\qquad8:903,\qquad9:84 \tag{3.2}
$$

In particular there is no six-row blocker. This excludes $(7,6)$.

## 4. The split $(8,5)$

Write

$$
\mathcal F=E(Q)\cup\{R\},\qquad A=R\cap X,\qquad Z=R\setminus X,
\qquad t=|Z| \tag{4.1}
$$

The clutter condition makes $A$ an independent set of $Q$. Relative to the
eight rows of $\mathcal F$, every point of $Z$ has the same singleton
incidence support $\{R\}$, but the $t$ actual points remain distinct. The
private-witness bound applied to $R\in B(\mathcal G)$ gives

$$
2\le|A|+t=|R|\le|\mathcal G|=5 \tag{4.2}
$$

Thus no ground-set bound has been imposed: all outside points are retained by
the exact multiplicity $t$, and (4.2) proves $t\le5$.

Let $\mathcal C=B(E(Q))$. Every transversal of $E(Q)\cup\{R\}$ contains a
member $C\in\mathcal C$. Its blockers are exactly the inclusion-minimal
members of

$$
\begin{aligned}
  \mathcal W(Q,A,Z)=
  &\{C:C\in\mathcal C,\ C\cap A\ne\varnothing\} \\
  &\cup\{C\cup\{a\}:C\in\mathcal C,\ C\cap A=\varnothing,\ a\in A\} \\
  &\cup\{C\cup\{z\}:C\in\mathcal C,\ C\cap A=\varnothing,\ z\in Z\}
\end{aligned} \tag{4.3}
$$

Indeed, the displayed members hit $R$ and every edge of $Q$. Conversely,
minimize any blocker first as a transversal of $E(Q)$. If its resulting
$C$ hits $A$, no extra point remains; otherwise minimality leaves exactly one
point of $A\cup Z$. This proves both directions of (4.3).

Equations (4.1)–(4.3) reduce every arbitrary-finite instance to exactly
$249576$ triples $(Q,A,t)$. The C++ implementation minimizes the candidate
family in (4.3). The independent Python verifier directly enumerates the
internal blockers on $X$ and adds the outside-point classes separately. They
agree on every output field.

There are $8400$ triples with exactly five blockers. Every one has a
three-point blocker. After imposing the required minimum row size four on
$\mathcal G$, $173304$ triples remain and their minimum blocker count is six.
Hence no admissible instance has $|\mathcal G|=5$, excluding $(8,5)$.

## 5. The split $(9,4)$

We strengthen frozen G4.10 Lemma 7.1.

### Lemma 5.1

`PROVED_CANDIDATE`: let $\mathcal D=\{D_1,D_2,D_3,D_4\}$ be a finite clutter.
If every row has size at least four, every two rows intersect, and
$\tau(\mathcal D)\ge2$, then

$$
|B(\mathcal D)|\ge10 \tag{5.1}
$$

Choose a smallest row $E=D_1$ and put $n=|E|$. For $j\in\{2,3,4\}$, define

$$
O_j=E\setminus D_j
$$

and, for every $x\in E$,

$$
w_x=\min_{j:x\in O_j}|O_j|,\qquad W=\sum_{x\in E}w_x \tag{5.2}
$$

Frozen G4.10 constructs at least $W$ blockers whose intersection with $E$ is
exactly one point, and proves

$$
W\ge\left\lceil\frac{n^2}{3}\right\rceil \tag{5.3}
$$

Now form the trace family

$$
\mathcal T=\{E,E\cap D_2,E\cap D_3,E\cap D_4\} \tag{5.4}
$$

Every proper trace is nonempty because the rows of $\mathcal D$ intersect,
and it is strictly smaller than $E$ because $\mathcal D$ is a clutter. The
condition $\tau(\mathcal D)\ge2$ rules out a singleton transversal of
$\mathcal T$. Hence every member of $B(\mathcal T)$ has at least two points.
Its private trace witnesses are also private rows of $\mathcal D$, so it is a
blocker of $\mathcal D$. These blockers lie inside $E$ and are disjoint from
the $W$ single-intersection classes. Therefore

$$
|B(\mathcal D)|\ge W+|B(\mathcal T)| \tag{5.5}
$$

If $n\ge5$, (5.3) gives $W\ge9$, while $B(\mathcal T)$ is nonempty. Suppose
$n=4$. Frozen G4.10 gives $W\ge6$.

- If $W\ge9$, one trace blocker suffices.
- If $W=8$ and $B(\mathcal T)$ had one row $Q$, blocker involution would make
  every singleton $\{q\}$ with $q\in Q$ a minimal trace. Since $|Q|\ge2$,
  two omissions would have size three. If the third omission has size
  $r\in\{1,2,3\}$, the frozen assignment bound gives

  $$
  W\ge r^2+3(4-r)\ge10
  $$

  Thus there are at least two trace blockers.
- If $W=7$, there are at least three trace blockers. Otherwise the preceding
  argument rules out one, so write $B(\mathcal T)=\{Q_1,Q_2\}$. Put

  $$
  c=|Q_1\cap Q_2|,\qquad
  p=|Q_1\setminus Q_2|,\qquad
  q=|Q_2\setminus Q_1|
  $$

  Blocker involution gives $c+pq$ proper minimal traces. There are at most
  three, while $p,q\ge1$ and $c+p,c+q\ge2$. Up to exchanging $p,q$, only

  $$
  (c,p,q)\in\{(1,1,1),(1,1,2),(2,1,1)\}
  $$

  remain. Direct substitution into the three omission sizes gives the
  respective lower bounds $W\ge8,9,10$, a contradiction.
- If $W=6$, the frozen $2+1+1$ omission partition supplies five trace
  blockers, so (5.5) is at least eleven.

This proves (5.1).

Return to $(9,4)$ and put $\mathcal D=\mathcal G$. Every row of
$\mathcal G$ strictly contains a Fano line. Any two such rows intersect,
every row has size at least four, and $\tau(\mathcal G)$ is the minimum row
size in $B(\mathcal G)=\mathcal F$, hence at least two. Lemma 5.1 gives
$|\mathcal F|\ge10$, contradicting $|\mathcal F|=9$.

Sections 3–5 exclude all lower splits in (2.1). The frozen exact dual excludes
all three upper splits. This proves the candidate exclusion of $P_{\mathrm F}$.

## 6. A three-point middle row at total sixteen

Let $\mathcal D$ and $\mathcal E=B(\mathcal D)$ be the two middle sides with

$$
|\mathcal D|+|\mathcal E|=16,\qquad
\min_{D\in\mathcal D}|D|\ge3,\qquad
\min_{E\in\mathcal E}|E|\ge3 \tag{6.1}
$$

Choose a uniformly random subset $R$ of the finite ground set. Exactly one of
the following types of events occurs:

$$
D\subseteq R\quad(D\in\mathcal D),\qquad
E\subseteq U\setminus R\quad(E\in\mathcal E) \tag{6.2}
$$

The union is exhaustive by blocker involution, and the two types are disjoint.
If all sixteen rows had size at least four, the union bound would give

$$
1\le\sum_{D\in\mathcal D}2^{-|D|}
+\sum_{E\in\mathcal E}2^{-|E|}\le1 \tag{6.3}
$$

Equality would force every row to have size four and all events in (6.2) to
be pairwise disjoint. But two different rows on the same side have a positive-
probability common event: a random set can contain their union. This
contradiction proves that at least one middle row has size three.

## 7. Excluding the split $(5,11)$

Let $|\mathcal D|=5$ and $|\mathcal E|=11$. A point cannot occur in four rows
of $\mathcal D$, since it could be extended by one point from the remaining
row to a transversal of size at most two. If every point had degree at most
two, the frozen support-multigraph theorem used in G4.11 would give at least
fifteen blockers. Hence some point $x$ occurs in exactly three rows.

The two rows $P,Q$ avoiding $x$ are disjoint; otherwise $x$ and a common point
would form a two-point transversal. Every choice $(p,q)\in P\times Q$ gives a
distinct minimal blocker $\{x,p,q\}$, so there are at least nine blockers
containing $x$. Delete $x$ from every row and take the inclusion-minimal
residual clutter $\mathcal R$. The residual-blocker lemma gives

$$
B(\mathcal R)=\{E\in\mathcal E:x\notin E\} \tag{7.1}
$$

Every residual row has size at least two, so the frozen residual lemma gives
at least two blockers avoiding $x$. Since $|\mathcal E|=11$, equality holds
throughout: exactly nine blockers contain $x$, and

$$
B(\mathcal R)=\{E_0,E_1\} \tag{7.2}
$$

The rows $E_0,E_1$ are disjoint. Otherwise, for $y\in E_0\cap E_1$, the pair
$\{x,y\}$ would hit all eleven rows of $\mathcal E$, contradicting
$\tau(\mathcal E)\ge3$. Both have size at least three. Blocker involution and
(7.2) now give

$$
\mathcal R=B(\{E_0,E_1\})
=\{\{u,v\}:u\in E_0,\ v\in E_1\} \tag{7.3}
$$

Thus $|\mathcal R|=|E_0||E_1|\ge9$, while $\mathcal R$ arose by minimizing
only five residual rows and therefore has at most five rows. This contradiction
excludes $(5,11)$. Exchanging the middle sides excludes $(11,5)$.

## 8. Point-degree reduction and degree-three branch of $(6,10)$

### Lemma 8.1

`PROVED_CANDIDATE`: every point has $\mathcal D$-degree at most three.

If $x$ lies in all six rows of $\mathcal D$, it is a singleton transversal.
If it lies in five rows, $x$ together with any point of the unique avoiding row
is a two-point transversal. Both contradict

$$
\tau(\mathcal D)=\min_{E\in\mathcal E}|E|\ge3
$$

It remains to rule out degree four. Let $P,Q$ be the two rows avoiding $x$.
They are disjoint; otherwise $x$ together with a point of $P\cap Q$ is a
two-point transversal. For every $(p,q)\in P\times Q$, the set
$\{x,p,q\}$ hits all six rows. The points $p$ and $q$ have private rows $P$
and $Q$, respectively. If $x$ had no private row, then $\{p,q\}$ would hit
the four rows containing $x$ as well as $P,Q$, again a two-point transversal.
Thus every $\{x,p,q\}$ is a minimal blocker. Since $|P|,|Q|\ge3$, there are
at least nine distinct blockers containing $x$.

Delete $x$ from every row and minimize the resulting family to a residual
clutter $\mathcal R$. Every row of $\mathcal R$ has size at least two. The
residual-blocker lemma gives

$$
B(\mathcal R)=\{E\in\mathcal E:x\notin E\}
$$

and the frozen residual lemma gives at least two such blockers. Hence
$|\mathcal E|\ge9+2=11$, contradicting $|\mathcal E|=10$. This proves the
lemma.

### Degree-three branch

Let $\mathcal D$ have six rows, let $\mathcal E=B(\mathcal D)$ have ten rows,
and suppose a point $x$ has degree three in $\mathcal D$. Write the three rows
avoiding $x$ as $\mathcal D_0$, the three rows containing $x$ as
$X_1,X_2,X_3$, and

$$
L_j=X_j\setminus\{x\},\qquad
\mathcal R=\min(\mathcal D_0\cup\{L_1,L_2,L_3\}) \tag{8.1}
$$

The residual-blocker lemma gives

$$
\mathcal T:=B(\mathcal R)=\{E\in\mathcal E:x\notin E\} \tag{8.2}
$$

Here $|\mathcal R|\le6$, every row of $\mathcal R$ has size at least two,
and every row of $\mathcal T$ has size at least three. Minimization in (8.1)
only retains some of the six displayed residual rows; it creates no new row.

The three rows of $\mathcal D_0$ have no common point, row sizes at least
three, and transversal number at least two. Write their six nonempty
incidence-class multiplicities as

$$
(p,q,r;x_{12},x_{13},x_{23})
$$

Every point has degree at most six on the ten-row blocker side. Degree at least
nine gives a two-point transversal; degree eight gives at least nine blockers
from the two avoiding rows; and degree seven gives at least seven blockers
from the three avoiding rows. Each contradicts the six-row double blocker.

Consequently the number $b_2$ of pair blockers in the three-row kernel is at
most six, and its total blocker count $b_2+b_3$ is at most ten. The exact
three-row formula and row incomparability leave, up to permuting the rows,
only

$$
\begin{array}{c|c|c}
(p,q,r;x_{12},x_{13},x_{23})&b_2&b_3\\
\hline
(1,1,1;1,1,1)&6&1\\
(1,2,2;1,1,0)&5&4\\
(1,1,3;2,0,0)&6&3
\end{array} \tag{8.3}
$$

For completeness, classify by the number of positive pair classes. With none,
$pqr\ge27$. With one, the row-size and clutter conditions force the last row
size at least three and leave only $(1,1,3;2,0,0)$. With two, the pair-count
bound forces both pair classes to equal one, after which the row sizes leave
$(1,2,2;1,1,0)$. With three, any multiplicity at least two makes $b_2\ge7$;
all three equal one, and the row sizes force $p=q=r=1$.

We now exclude all three kernels.

### Kernel C

Use the realization

$$
\mathcal D_0=
\{\{a,u_1,u_2\},\{b,u_1,u_2\},\{c_1,c_2,c_3\}\} \tag{8.4}
$$

Its six pair blockers are $\{u_i,c_j\}$, and its three triple blockers are
$\{a,b,c_j\}$. Every pair image under the injection through $x$ must acquire
$x$, since $\mathcal E$ has no two-point row. These six rows exhaust the
maximum possible $\mathcal E$-degree of $x$. Hence

$$
\mathcal T=
\{\{a,b,c_1\},\{a,b,c_2\},\{a,b,c_3\},Q\} \tag{8.5}
$$

If $Q$ contained $a$ or $b$, $B(\mathcal T)=\mathcal R$ would contain a
singleton row. Thus $Q$ avoids $a,b$. For every $q\in Q$, both
$\{a,q\}$ and $\{b,q\}$ are distinct minimal transversals of $\mathcal T$.
If $Q$ meets $C_0=\{c_1,c_2,c_3\}$, then $C_0$ is a seventh blocker. If it
does not, every $C_0\cup\{q\}$ is an additional blocker. Since $|Q|\ge3$,
both cases contradict $|\mathcal R|\le6$.

### Kernel B

Use the realization

$$
\mathcal D_0=
\{\{a,u,v\},\{b_1,b_2,u\},\{c_1,c_2,v\}\} \tag{8.6}
$$

Its five pair blockers are

$$
\{u,v\},\{u,c_1\},\{u,c_2\},\{v,b_1\},\{v,b_2\}
$$

and its four triple blockers are $\{a,b_i,c_j\}$. The pair images consume
five occurrences of $x$.

First suppose no triple image contains $x$. Then $\mathcal T$ consists of all
four triples and one additional row $Q$. The row $Q$ avoids $a$, or
$\mathcal R$ has singleton $\{a\}$. Put

$$
B_0=\{b_1,b_2\},\qquad C_0=\{c_1,c_2\}
$$

For every $q\in Q$, $\{a,q\}$ is a blocker. If $Q$ meets $B_0$, then $B_0$
is one blocker; otherwise every $B_0\cup\{q\}$ is a blocker. The same
dichotomy holds for $C_0$, and the three classes are disjoint. Therefore

$$
|\mathcal R|=
|Q|+
\begin{cases}1&Q\cap B_0\ne\varnothing\\|Q|&Q\cap B_0=\varnothing\end{cases}
+\begin{cases}1&Q\cap C_0\ne\varnothing\\|Q|&Q\cap C_0=\varnothing\end{cases}
\tag{8.7}
$$

The bounds $|Q|\ge3$ and $|\mathcal R|\le6$ force $Q$ to meet both pairs and
make every row of $\mathcal R$ a pair. Its cardinality is five or six.

Now suppose one triple image contains $x$. Up to relabeling, the three
triple rows in $\mathcal T$ are

$$
\{a,b_1,c_1\},\{a,b_1,c_2\},\{a,b_2,c_1\} \tag{8.8}
$$

together with $Q$. Again $Q$ avoids $a$. After deleting $a$, the three edges
form a four-vertex path whose minimal vertex covers are

$$
\{b_1,c_1\},\qquad\{b_1,b_2\},\qquad\{c_1,c_2\} \tag{8.9}
$$

If $Q$ misses one of these covers, that cover joined to each $q\in Q$, the
rows $\{a,q\}$, and one blocker from each of the other two cover classes give
at least eight blockers. Thus $Q$ meets all three covers. It follows that
$|Q|=3$, $|\mathcal R|=6$, and every row of $\mathcal R$ is again a pair.

In either subcase, none of the three length-three rows in (8.6) belongs to
$\mathcal R$. Equation (8.1) then says that all rows of $\mathcal R$ must come
from only $L_1,L_2,L_3$, so $|\mathcal R|\le3$. This contradicts the value
five or six above. If the tenth row rather than a triple image contained $x$,
all four triple rows would lie in $\mathcal T$ and give singleton $\{a\}$;
that case is already impossible.

### Kernel A

Use the realization

$$
\mathcal D_0=
\{\{a,u,v\},\{b,u,w\},\{c,v,w\}\} \tag{8.10}
$$

The six pair images all contain $x$, while the unique triple blocker
$\{a,b,c\}$ avoids it. Thus

$$
\mathcal T=\{\{a,b,c\},Q_1,Q_2,Q_3\} \tag{8.11}
$$

This is an exact arbitrary-finite reduction to a four-row incidence kernel.
Every row of $\mathcal T$ has size from three through six by the private-row
bound $|T|\le|\mathcal R|\le6$. Since $\tau(\mathcal T)\ge2$, no point has
full four-row incidence support. There are therefore only fourteen nonempty
proper supports. Actual points with one support retain an arbitrary positive
multiplicity subject to the row-size bound.

The strict C++ checker and independent Python implementation enumerate all
$16383$ active support masks, all multiplicities, and all row permutations.
There are $95$ feasible multiplicity vectors in nine row-permutation classes:

$$
\begin{array}{c|c|c}
|\mathcal R|&\text{pair rows in }\mathcal R&\text{vectors}\\
\hline
5&5&6\\
6&5&12\\
6&6&77
\end{array} \tag{8.12}
$$

For every vector, both implementations expand the actual points and recompute
$\mathcal R=B(\mathcal T)$. If $|\mathcal R|=6$, all three rows in (8.10)
must belong to $\mathcal R$, because only three additional residual rows
$L_j$ are available. If $|\mathcal R|=5$, at least two must belong. The
checker exhausts every choice of the length-three row $\{a,b,c\}$, all six
labelings of its points, and every choice of distinct $u,v,w$. It returns zero
compatible extensions. The independent verifier agrees on every class and
count.

Kernels A, B, and C are all impossible. Hence the degree-three branch of
$(6,10)$ is excluded. It remains to treat the branch in which every point on
the six-row side has degree at most two. This is an actual loop-multigraph
problem, not an unbounded-incidence problem.

## 9. The low-degree branch of $(6,10)$

Suppose every point on the six-row side $\mathcal D$ has degree at most two.
Represent its active points as actual loops and nonloop edges on the six row
indices. Choose an inclusion-minimal set $J$ of actual points for which every
row vertex retains degree at least three.

Every minimal edge cover of $J$ is a blocker of $\mathcal D$. Indeed, it hits
all six original rows, and support-minimality gives a private row for every
selected actual point. Parallel actual points remain different choices.

Every point of $J$ touches a degree-three vertex. Otherwise that point could
be deleted without violating the six degree lower bounds. Let $l$ be the
number of degree-three vertices. Every other vertex has degree at least four,
and every incidence at such a vertex is paired with an incidence at a
degree-three vertex. Hence

$$
4(6-l)\le3l \tag{9.1}
$$

so $l\in\{4,5,6\}$. Up to permuting the row vertices, put the degree-three
vertices first. Every positive loop or edge support touches one of them. Its
actual multiplicity is bounded by the exact degree three at that endpoint.
This is a finite reduction with no ground-set bound.

There are 21 loop and nonloop supports and 562 inclusion-minimal support
covers. For a multiplicity vector $m$, the number of actual minimal edge
covers is exactly

$$
N(m)=\sum_M\prod_{s\in M}m_s \tag{9.2}
$$

where $M$ ranges over the support covers. The C++ checker and independent
Python implementation enumerate every vector with the first $l$ degrees
equal to three and the other degrees at least four. They do not require the
six rows to remain a clutter, so the enumeration is an overfamily of the
possible cores. The exact results are:

| $l$ | Vectors | $\nu=0$ | $\nu=1$ | $\nu=2$ | $\nu=3$ |
|---:|---:|---:|---:|---:|---:|
| 4 | 5244 | -- | -- | 54 | 24 |
| 5 | 57080 | -- | 195 | 48 | 21 |
| 6 | 44288 | 729 | 171 | 45 | 15 |

Each entry in the last four columns is the minimum of $N(m)$ at the indicated
matching number. Thus $J$ has at least fifteen minimal edge covers. They give
at least fifteen distinct blockers of $\mathcal D$, contradicting
$|B(\mathcal D)|=10$. This excludes the low-degree branch and completes the
exclusion of $(6,10)$. Blocker duality excludes $(10,6)$.

## 10. Excluding the split $(8,8)$

Let $|\mathcal D|=|\mathcal E|=8$ with
$\mathcal E=B(\mathcal D)$. First bound point degrees on both sides. Degree at
least seven gives a transversal of size at most two. Degree six leaves two
rows; their pair blockers give at least nine injection images. Thus every
point initially has degree at most five.

If $x$ had degree five, the three rows avoiding $x$ would have at most eight
blockers. Every pair blocker acquires $x$, so their number is at most five.
The exact three-row formula in Section 8 has no integer solution with
$b_2\le5$ and $b_2+b_3\le8$: its only solution below total ten with
$b_2\le5$ is Kernel B, which has total nine. Therefore every point on both
sides has degree at most four.

Suppose $x$ has degree four in $\mathcal D$. The four rows avoiding $x$ form
a kernel with row sizes from three through eight, at most eight blockers, and
at most four pair blockers. Its points use the fourteen nonempty proper
supports on four rows; the full support is excluded by transversal number at
least two. Row sizes bound every actual multiplicity.

The exact four-row enumeration checks all 16383 active support masks. It
retains 49 multiplicity vectors in four row-permutation classes:

$$
\begin{array}{c|c|c}
|B|&\text{pair blockers}&\text{vectors}\\
\hline
7&3&1\\
8&4&48
\end{array} \tag{10.1}
$$

For the three eight-blocker classes, the injection through $x$ determines the
opposite side: all four pair blockers acquire $x$ and every other blocker
avoids it. The seven-blocker class is the $K_4$ edge clutter. Its three pair
blockers acquire $x$; at most one of its four other blockers may acquire
$x$, and one further row remains. Existing points may enter that row whenever
their degree permits it. All new points have its singleton incidence support,
with exact multiplicity bounded by row size eight.

The semantic checker reconstructs every resulting blocker pair. It tests
1432 extension candidates and finds none with eight rows on each side, row
sizes at least three, point degrees at most four, and the original four kernel
rows. Hence degree four is impossible on either side; every point has degree
at most three.

Section 6 supplies a three-point row $T$. By symmetry put $T\in\mathcal D$.
It covers all eight rows of $\mathcal E$. At least two points of $T$ have
$\mathcal E$-degree three. Fix one such point $x$ and delete the three rows
containing it. The remaining five-row kernel has row sizes from three through
eight, at most eight blockers, at most three pair blockers, and point supports
of rank at most three.

There are 25 nonempty rank-at-most-three supports on five rows. The C++
enumerator checks all $2^{25}-1=33554431$ active masks, retains parallel
actual points through their multiplicities, and obtains:

```text
support-feasible masks:  96,148
multiplicity vectors:     1,890
row-permutation classes:     24
blockers 6 / 7 / 8:      20 / 470 / 1,400 vectors
```

Every retained vector has exactly three pair blockers. Their images acquire
$x$ and use all three allowed occurrences of $x$ on $\mathcal D$. If the
kernel has six, seven, or eight blockers, respectively two, one, or zero
additional $x$-free rows remain.

For two additional rows, every new actual point has one of the three supports
consisting of the first row, the second row, or both. The extension checker
enumerates all three multiplicities, every allowed incidence of an existing
point, and the one-row cases. It recomputes blockers by choice-union
minimization. Across the 24 kernel classes it checks 2514 candidates and finds
zero valid extensions. This excludes $(8,8)$.

## 11. Excluding the split $(7,9)$

Let $|\mathcal D|=7$ and $|\mathcal E|=9$, with
$\mathcal E=B(\mathcal D)$. We first sharpen the point-degree bounds.

### Lemma 11.1

`PROVED_CANDIDATE`: every point has $\mathcal D$-degree at most three and
$\mathcal E$-degree at most four.

A point in at least six rows of $\mathcal D$ gives a transversal of size at
most two. If it lies in five rows, the two avoiding rows must be disjoint.
Their point pairs give at least nine blockers containing the point. These
would exhaust $\mathcal E$, making the point a singleton transversal of
$\mathcal E$. Thus every $\mathcal D$-degree is at most four.

On the nine-row side, degrees at least seven are excluded by the same
one-row or two-row argument. At degree six, the three avoiding rows have at
least seven blockers. If their injection into $\mathcal D$ has only seven
images, equality in the three-row formula leaves at least six pair blockers.
All six acquire the chosen point, contradicting the preliminary
$\mathcal D$-degree bound four.

Suppose a point has $\mathcal E$-degree five. Its four avoiding rows have at
most seven blockers and at most four pair blockers. The exact four-row
classification has one such class: the six-edge incidence clutter of
$K_4$. Its blockers are three perfect matchings and four stars. The three
matchings acquire the chosen point. If no star acquires it, the seven images
form the self-blocking Fano clutter and have seven, not nine, blockers. If
one star acquires it, direct blocker minimization gives ten blockers. More
than one star would violate the preliminary degree-four bound. Hence every
$\mathcal E$-degree is at most four.

Finally, a point of $\mathcal D$-degree four leaves three avoiding rows with
at most nine blockers and at most four pair blockers. The exact three-row
formula has no integer solution under those two bounds and row-size minimum
three. Therefore every $\mathcal D$-degree is at most three.

### A three-point row on the nine-row side

Suppose $T\in\mathcal E$ has size three. It covers all seven rows of
$\mathcal D$. Lemma 11.1 gives a point $x\in T$ of
$\mathcal D$-degree three. The four rows avoiding $x$ form a kernel
$\mathcal K$ with:

- row sizes from three through nine;
- at most nine blockers and at most four pair blockers;
- fourteen nonempty proper incidence supports.

The proper-support condition follows from transversal number at least two.
Row sizes bound every actual multiplicity, so this is an exact
arbitrary-finite reduction.

The C++ enumerator and independent Python implementation check all 16383
active support masks. They obtain 136 multiplicity vectors in eleven
row-permutation classes:

| Blockers | Pair blockers | Vectors |
|---:|---:|---:|
| 7 | 3 | 1 |
| 8 | 4 | 48 |
| 9 | 3 | 12 |
| 9 | 4 | 75 |

For every pair blocker, injection through $x$ is forced to add $x$. Every
other kernel blocker either remains unchanged or acquires $x$. At most two
further rows are needed to reach nine. An existing point can enter those
rows whenever its degree permits it. A new point has one of the two private
supports or the shared support when two rows are added. Thus the extension
enumeration retains fresh private points, fresh shared points, parallel
actual points, and every allowed multiplicity.

The independent C++ and Python semantic checkers reconstruct the complete
blocker pair for every extension. Their per-class counts agree exactly:

```text
kernel classes:          11
extension candidates: 138161
valid extensions:         0
```

Therefore the nine-row side cannot contain a three-point row.

### A three-point row only on the seven-row side

Now let $T=\{x,a,b\}\in\mathcal D$ have size three and suppose every row of
$\mathcal E$ has size at least four. The row $T$ covers all nine rows of
$\mathcal E$.

First suppose some point of $T$, say $x$, has $\mathcal E$-degree four. The
five rows avoiding $x$ form a kernel with row sizes from four through seven,
at most seven blockers, and at most three pair blockers. If a kernel point
$y$ had degree four, let $R$ be the unique row avoiding it. For every
$z\in R$, the pair $\{y,z\}$ covers the kernel. The row $R$ is private for
$z$. Also, $z$ cannot occur in all four rows containing $y$, because then its
global $\mathcal E$-degree would be at least five. Thus one of those rows is
private for $y$, so $\{y,z\}$ is minimal. Since $|R|\ge4$, this gives four
pair blockers, a contradiction.

Every point of the five-row kernel therefore has degree at most three. The
frozen G4.11 five-row enumeration is complete for row sizes from three
through seven, at most seven blockers, and at most three pair blockers. Its
490 multiplicity vectors form eight row-permutation classes, and every class
has a row of size three. This contradicts the present row-size minimum four.

It remains that every point of $T$ has $\mathcal E$-degree at most three.
The nine rows all meet $T$, so all three degrees equal three and every row
meets $T$ exactly once. After deleting the three rows containing $x$, write
the remaining kernel as

$$
\mathcal K=\{A_1,A_2,A_3,B_1,B_2,B_3\}
$$

where $a\in A_i$, $b\in B_i$, and the other point of $\{a,b\}$ is absent.
The pair $\{a,b\}$ is a blocker of $\mathcal K$. Hence

$$
|B(\mathcal K)|\le7,
\qquad
|\{Q\in B(\mathcal K):|Q|=2\}|\le3 \tag{11.1}
$$

Put $A_i'=A_i\setminus\{a\}$. The blocker family of the three $A_i$ is
$\{\{a\}\}\cup B(\{A_i'\})$, and it injects into $B(\mathcal K)$. If the
three $A_i'$ had no common point, the three-row formula would give at least
seven blockers, contradicting the first bound in (11.1). Thus they have a
common point. The same holds on the $B$ side.

Every common point on the $A$ side gives a pair blocker with $b$, and every
common point on the $B$ side gives one with $a$. Together with $\{a,b\}$,
the second bound in (11.1) forces unique common points $c$ and $d$.
Delete $c$ from the three $A_i'$ and delete $d$ from the three $B_i'$.
Call the resulting three-row clutters $\mathcal A$ and $\mathcal B$, and put

$$
r_A=|B(\mathcal A)|,
\qquad
r_B=|B(\mathcal B)|
$$

The two three-row injections into $B(\mathcal K)$ have sizes $2+r_A$ and
$2+r_B$. Their intersection consists of $\{a,b\}$ and at most
$\min(r_A,r_B)$ common residual images. Consequently

$$
|B(\mathcal K)|\ge3+\max(r_A,r_B)
$$

and (11.1) gives $r_A,r_B\le4$.

Both $\mathcal A$ and $\mathcal B$ have three rows, row sizes from two
through five, no common point, and at most four blockers. The exact
three-row formula gives nineteen labelled multiplicity vectors and six
row-permutation classes. A global actual point is obtained by leaving a
point copy on one side or matching one copy from each side. The global
degree-four bound permits exactly the matches whose two local support ranks
sum to at most four. The special points $c$ and $d$ carry full three-row
support on their own sides and are retained in the same matching rule.

The C++ enumerator checks all 90898 labelled couplings. The independent
Python implementation reproduces every field. Their exact pair-blocker
histogram is:

| Pair blockers | Couplings |
|---:|---:|
| 4 | 22485 |
| 5 | 38832 |
| 6 | 23313 |
| 7 | 5614 |
| 8 | 634 |
| 9 | 20 |

Every coupling has at least four pair blockers, contradicting (11.1). This
excludes the last orientation with a three-point row only on the seven-row
side.

Section 6 guarantees a three-point row on at least one side. Both locations
are now impossible, so the split $(7,9)$ is excluded. Blocker duality excludes
$(9,7)$.

## 12. Global deduction and evidence boundary

Sections 2–5 exclude the Fano profile. Sections 6–11 exclude every ordered
split of the sixteen-member middle pair. Therefore both profiles in the
frozen slack reduction are impossible. No fifty-four-member family survives
the arbitrary-finite canonical framework.

The frozen G4.11 result gives $\operatorname{sat}(7)\ge54$, while the frozen
construction gives $\operatorname{sat}(7)\le55$. Excluding total 54 therefore
gives the candidate conclusion

$$
\operatorname{sat}(7)=55 \tag{12.1}
$$

- `PROVED_CANDIDATE`: the arbitrary-finite reductions, Lemma 5.1, the
  three-point-row lemma, all middle-split exclusions, and (12.1) relative to
  the frozen inputs.
- `COMPUTED`: the raw C++ enumerations and independent Python replays. They
  become proof dependencies only through the proved finite reductions.
- `UNKNOWN`: isolated-Referee acceptance, novelty, priority, and a Lean
  formalization of (12.1).
- No claim/status update, publication, push, expert contact, novelty
  statement, or next gate is included.
