# P0054 G4.13 scratch: pure residual lemmas

```text
STATUS: PROVED_CANDIDATE
SCOPE: C1_FOUR_ROW_AND_C2_FIVE_ROW_RESIDUAL_BRANCHES
RESULT: REMOVE_ALL_REMAINING_RESIDUAL_ENUMERATIONS
NETWORK: MATHEMATICS_OFFLINE
```

All clutters below are finite. A blocker is an inclusion-minimal transversal.
The identity $B(B(\mathcal H))=\mathcal H$ is used only for finite clutters.

## Two small facts

### Two blockers

Let $B(\mathcal L)=\{Q_1,Q_2\}$, where both blockers have size at least two.
Put

$$
\begin{aligned}
I&=Q_1\cap Q_2,\\
P&=Q_1\setminus Q_2,\\
Q&=Q_2\setminus Q_1.
\end{aligned}
$$

Blocker involution gives

$$
\mathcal L
=
\{\{z\}:z\in I\}
\cup
\{\{p,q\}:p\in P,\ q\in Q\}.
\tag{1}
$$

Thus intersecting blockers force a singleton row in $\mathcal L$. Disjoint
blockers force at least four pair rows in $\mathcal L$.

If $B(\mathcal L)=\{Q\}$, involution instead gives

$$
\mathcal L=\{\{q\}:q\in Q\}.
\tag{2}
$$

### Three blockers

Let $\mathcal L$ be a three-row clutter. Assume every row has size at least
two and $B(\mathcal L)$ has no singleton row. Then

$$
|B(\mathcal L)|\ge3.
\tag{3}
$$

If equality holds, all three rows of $\mathcal L$ are pairs.

To prove the equality statement, use the exact three-row partition. Let
$p,q,r$ be the three private multiplicities, and let $x,y,z$ be the three
pairwise multiplicities. The triple intersection is empty because the blocker
has no singleton row. Then

$$
|B(\mathcal L)|
=xy+xz+yz+xr+yq+zp+pqr.
\tag{4}
$$

If $pqr>0$, consider the value of the product. For $pqr=1$, all three private
multiplicities equal one. The positive pairwise classes have no isolated row,
so two such classes contribute one quadratic and two linear terms, in
addition to $pqr=1$. For $pqr=2$, the private values are $(1,1,2)$. The two
rows with private value one either share a positive pairwise class, which
contributes at least two through a linear term, or require two classes, which
contribute at least one each. For $pqr=3$, one positive pairwise class already
raises the total to four. Values at least four need no additional estimate.
Thus the right side is at least four whenever $pqr>0$. If $pqr=0$, exchange
the rows so that $p=0$. Incomparability gives $x,y>0$.
Equation (4) becomes

$$
xy+z(x+y)+xr+yq.
\tag{5}
$$

For $z>0$, equality at three forces $x=y=z=1$ and $q=r=0$. For $z=0$, it
forces $x=y=q=r=1$. In either case every input row is a pair. Equations (1)
and (2) rule out one or two blockers and prove (3).

## Four-row classification

### Lemma 1

`PROVED_CANDIDATE`: let $\mathcal T$ be a four-row clutter such that every row
has size at least two and at most one row is a pair. Put

$$
\mathcal R=B(\mathcal T).
$$

Assume:

- $|\mathcal R|\le5$;
- every row of $\mathcal R$ has size at least two;
- at most three rows of $\mathcal R$ are pairs.

Then $\mathcal R$ has exactly three pair rows and two triple rows. Its two
triple rows intersect in two points.

### Proof

If every row of $\mathcal T$ has size at least three, the pure four-large-row
lemma in `/tmp/p0054_g413_small_residual_lemmas.md` applies. It gives either
$|\mathcal R|\ge6$ or at least four pair rows. Both alternatives contradict
the assumptions. Hence $\mathcal T$ has one pair row

$$
E=\{p,q\}.
$$

No other row contains both $p$ and $q$, since $\mathcal T$ is a clutter.
Partition the other three rows into:

- $X$: rows containing $p$;
- $Y$: rows containing $q$;
- $Z$: rows containing neither endpoint.

If $Z$ is empty and all rows lie on one side, $p$ or $q$ is a singleton
blocker. If the split is $2+1$, the set $E$ is a pair blocker. The lone-side
row supplies at least two more pair blockers. The two-row residual on the
other side either supplies at least three blockers or supplies one pair and
one triple. The first alternative gives at least six blockers. The second
gives at least four pair blockers. Thus $Z$ is nonempty.

Suppose $|Z|=1$ and the other two rows lie on one side. The row in $Z$ has at
least three points, each of which forms a pair blocker with the endpoint on
that side. The opposite residual has three rows of size at least two. It has
no singleton blocker, since the three pair blockers already exhaust the pair
budget. Equations (1) and (2) show that this residual has at least three
blockers. Hence $|\mathcal R|\ge6$.

Suppose $|Z|=2$. The remaining row lies on one side. Blockers using the
endpoint on that side are obtained from the two $Z$ rows. The two rows have
size at least three, so they have at least three blockers. Blockers using the
opposite endpoint come from the residual formed by the remaining row and the
two $Z$ rows. That residual has at most three rows, and every row has size at
least two. One blocker is impossible by (2).

If it has two blockers, intersecting blockers would reconstruct a singleton
minimal row. Disjoint blockers reconstruct only pair rows. Only the residual
of the row outside $Z$ can be a pair. Hence the residual reduces to one pair
and its two blockers are singletons. The two large $Z$ rows can have only
three blockers when they meet in two points and have one private point each.
Their blockers then consist of two singletons and one pair. After adjoining
the two endpoints of $E$, the five resulting rows include four pairs and only
one triple. This contradicts the three-pair limit. In every other case the
two disjoint blocker families have total size at least six.

If all three rows lie in $Z$, every blocker $D$ of those rows gives the two
distinct blockers $D\cup\{p\}$ and $D\cup\{q\}$. The three-row family has at
least three blockers. One blocker would reconstruct singleton rows. Two
blockers would reconstruct only singleton and pair rows. Both alternatives
contradict the three large input rows. This gives at least six blockers.

The only remaining distribution has one row of each type. Write

$$
\begin{aligned}
A&=\{p\}\cup A_0,\\
C&=\{q\}\cup C_0,\\
N&\in Z.
\end{aligned}
$$

Set

$$
\begin{aligned}
u&=|A_0\cap N|, & a&=|A_0\setminus N|,\\
v&=|C_0\cap N|, & b&=|C_0\setminus N|,\\
n&=|N|, & w&=|N\setminus(A_0\cup C_0)|.
\end{aligned}
\tag{6}
$$

The blockers are exactly:

- $u+v$ pairs, obtained from the two intersections with $N$;
- $a(n-u)+b(n-v)$ triples using exactly one of $p,q$;
- $w$ triples using both $p,q$.

Therefore

$$
|\mathcal R|=u+v+a(n-u)+b(n-v)+w.
\tag{7}
$$

The row-size and clutter conditions give

$$
\begin{aligned}
a+u&\ge2, & b+v&\ge2, & n&\ge3,\\
n-u&\ge1, & n-v&\ge1, & w&\ge n-u-v.
\end{aligned}
\tag{8}
$$

Put $s=u+v$. The pair budget gives $s\le3$. If $s=0$, the triple count in
(7) is at least twelve. If $s=1$, it is at least ten. If $s=2$, it is at
least five. These lower bounds follow directly from (8), treating
$(u,v)=(1,1)$ and $(2,0)$ separately in the last case.

Hence $s=3$. The cases $(u,v)=(3,0)$ and $(0,3)$ force $n\ge4$ and at least
eight triples. For $(u,v)=(2,1)$, the triple count is

$$
a(n-2)+b(n-1)+w.
\tag{9}
$$

The total-row bound makes (9) at most two. Equations (8) make it at least two,
so equality holds and

$$
(n,a,b,w)=(3,0,1,0).
\tag{10}
$$

The case $(u,v)=(1,2)$ exchanges the two endpoints and gives
$(n,a,b,w)=(3,1,0,0)$.

In both cases $A_0\cap N$ and $C_0\cap N$ partition $N$. The two triple
blockers share one endpoint of $E$ and the unique point outside $N$ on the
opposite row. Their intersection therefore has size two. Equation (7) gives
three pairs and two triples. This proves the lemma.

## At-most-five-row lower bound

### Lemma 2

`PROVED_CANDIDATE`: let $\mathcal H$ be a clutter with

$$
3\le|\mathcal H|\le5.
$$

Assume every row has size at least two, at most three rows are pairs, and

$$
\tau(\mathcal H)\ge3.
$$

Then

$$
|B(\mathcal H)|\ge6.
\tag{11}
$$

No bound on the ground-set size, row sizes, point degrees, or incidence
multiplicities is required.

### Proof

If every row has size at least three, the four- and five-row cases follow from
the accepted G4.9 bounds. For three rows, the condition
$\tau(\mathcal H)\ge3$ gives a direct proof: the rows are pairwise disjoint,
so their blocker count is at least $3^3=27$. Fix a pair row

$$
E=\{p,q\}.
$$

No other row contains both endpoints. Partition the other
$|\mathcal H|-1$ rows into $X,Y,Z$ as in Lemma 1. The condition
$\tau(\mathcal H)\ge3$ gives $|Z|\ge1$.

Define the two residual clutters

$$
\begin{aligned}
\mathcal L_p&=\min\bigl(\{Y\setminus\{q\}:Y\in\mathcal Y\}\cup\mathcal Z\bigr),\\
\mathcal L_q&=\min\bigl(\{X\setminus\{p\}:X\in\mathcal X\}\cup\mathcal Z\bigr).
\end{aligned}
\tag{12}
$$

Every $D\in B(\mathcal L_p)$ gives the blocker $D\cup\{p\}$ of $\mathcal H$.
The row $E$ is private for $p$, and the residual private rows remain private
for the points of $D$. The corresponding statement holds for $q$. The two
families are disjoint, so

$$
|B(\mathcal H)|
\ge
|B(\mathcal L_p)|+|B(\mathcal L_q)|.
\tag{13}
$$

Neither residual blocker has a singleton row. Such a singleton would combine
with $p$ or $q$ to form a two-point transversal of $\mathcal H$.

### Three rows

There are two rows outside $E$. At least one lies in $Z$.

If both lie in $Z$, then

$$
\mathcal L_p=\mathcal L_q=\mathcal Z.
$$

The two $Z$ rows are disjoint, since their blocker has no singleton. They
therefore have at least four blockers. Equation (13) gives at least eight.

If exactly one row lies in $Z$, the other lies in $X$ or $Y$. On the opposite
side, the residual clutter consists of the single $Z$ row and has singleton
blockers. This contradicts $\tau(\mathcal H)\ge3$. Thus (11) holds for three
rows.

### Four rows

There are three rows outside $E$. Put $c=|Z|$.

If $c=3$, then $\mathcal L_p=\mathcal L_q=\mathcal Z$. The three-row fact
gives at least four blockers, since at most two $Z$ rows are pairs. Equation
(13) gives at least eight.

Suppose $c=2$. Exchange $p,q$ so that the remaining row lies in $X$. The two
$Z$ rows are disjoint, so

$$
|B(\mathcal L_p)|=|Z_1||Z_2|\ge4.
$$

The clutter $\mathcal L_q$ has at most one singleton source. Its blocker count
cannot be one: equation (2) would require at least two singleton minimal rows.
Hence (13) gives at least six.

It remains that $c=1$. The other two rows cannot both lie on one side, since
the opposite residual would consist of one row and have singleton blockers.
Thus $|X|=|Y|=1$. Each residual in (12) consists of the $Z$ row and one
endpoint-deleted row. If the latter were contained in $Z$, the residual would
have singleton blockers. The reverse containment would violate the original
clutter condition. Hence the two residual rows are incomparable. They are
disjoint because the residual blocker has no singleton.

If both endpoint rows are large, the two residual blocker counts are at least
$2|Z|$, so their sum is at least eight. If exactly one endpoint row is a pair,
the counts are at least $|Z|$ and $2|Z|$, so their sum is at least six. If
both are pairs, the pair budget makes $Z$ large. Both residual blocker counts
then equal $|Z|\ge3$. This proves (11) for four rows.

### Five rows

Write $c=|Z|$. We treat $c=4,3,2,1$.

### Four avoiding rows

Here $\mathcal L_p=\mathcal L_q=\mathcal Z$. The four rows in $Z$ include at
most two pairs. Equations (1) and (2) show that $|B(\mathcal Z)|\le2$ would
force a singleton row or four pair rows. Hence

$$
|B(\mathcal L_p)|=|B(\mathcal L_q)|\ge3.
$$

Equation (13) proves (11).

### Three avoiding rows

Exchange $p,q$ so that $|X|=1$ and $|Y|=0$. The three-row fact gives

$$
|B(\mathcal L_p)|=|B(\mathcal Z)|\ge4,
$$

because equality at three would make all three $Z$ rows pairs. There are at
most two pair rows outside $E$. The clutter $\mathcal L_q$ has at most one
singleton source, namely the residual of the sole $X$ row. Equations (1) and
(2) therefore give $|B(\mathcal L_q)|\ge2$. Equation (13) gives at least six
blockers.

### Two avoiding rows

First suppose $|X|=2$ and $|Y|=0$. The two $Z$ rows are disjoint, since a
common point would produce a singleton blocker of $\mathcal L_p$. Hence

$$
|B(\mathcal L_p)|=|Z_1||Z_2|\ge4.
\tag{14}
$$

If $|B(\mathcal L_q)|\ge2$, (13) finishes the case. If it equals one,
equation (2) requires at least two singleton rows in $\mathcal L_q$. Both $X$
rows must then be pair rows. The pair budget makes both $Z$ rows large, so
(14) is at least nine. The case $|X|=0,|Y|=2$ exchanges the endpoints.

Now suppose $|X|=|Y|=1$. Each residual blocker family has at least two rows,
because each side has at most one singleton source. Assume
$|B(\mathcal L_p)|=2$. Equation (1) forces exactly one singleton row and one
or two pair rows in $\mathcal L_p$. The singleton comes from a pair row in
$Y$.

Two residual pair rows would make both $Z$ rows pairs. Together with $E$ and
the pair row in $Y$, this exceeds the pair budget. Hence one $Z$ row is a
pair, while the other contains the singleton point and disappears during
minimization. The pair row in $Y$, the surviving pair row in $Z$, and $E$
exhaust the pair budget. The $X$ row is therefore large.

The pair $Z$ row survives in $\mathcal L_q$. It cannot contain, or be
contained in, the residual of the $X$ row without creating a containment
between two rows of the original clutter. If the residual of the $X$ row is
contained in the large $Z$ row, $\mathcal L_q$ has two disjoint rows of size
at least two and therefore at least four blockers. Otherwise it has three
rows of size at least two. The surviving large $Z$ row prevents all three
from being pairs. The three-row fact again gives at least four blockers.
Thus

$$
|B(\mathcal L_p)|+|B(\mathcal L_q)|\ge2+4=6.
$$

The argument with $p,q$ exchanged covers the other residual side.

### One avoiding row

The split $|X|=3,|Y|=0$ is impossible: $\mathcal L_p$ has one row and hence
has singleton blockers. Exchange $p,q$ if needed, and assume

$$
\begin{aligned}
|X|&=2,\\
|Y|&=1,\\
Z&=\{N\}.
\end{aligned}
$$

The two rows in $\mathcal L_p$ are incomparable and disjoint. Therefore

$$
|B(\mathcal L_p)|=|Y\setminus\{q\}||N|.
\tag{15}
$$

If $Y$ is large and $N$ is large, (15) is at least six. If $Y$ is large and
$N$ is a pair, (15) is at least four. At most one $X$ row is then a pair, so
equations (1) and (2) give $|B(\mathcal L_q)|\ge2$. This also gives six.

Suppose $Y$ is a pair. If $N$ is also a pair, (15) equals two and both $X$
rows are large. All three rows of $\mathcal L_q$ have size at least two. If
its blocker count is three, the three-row equality case makes all three
residual rows pairs. Every point $z\in N$ then gives another blocker
$\{p,q,z\}$ of $\mathcal H$. If its blocker count is at least four, (13)
already gives six. Both alternatives prove (11).

It remains that $Y$ is a pair and $N$ is large. Equation (15) gives at least
three blockers. The blocker count of $\mathcal L_q$ cannot be one, since that
would require at least two singleton minimal rows and only one $X$ row can
supply one. If $|B(\mathcal L_q)|\ge3$, (13) finishes the proof. If its
blocker count is two, equation (1) forces one $X$ row to be a pair. The other
$X$ residual is a pair, and the large row $N$ disappears during minimization
because it contains either that residual pair or the singleton point.

Let $u$ be the singleton point from the pair $X$ row. Choose
$z\in N\setminus\{u\}$, which is possible because $|N|\ge3$. The set
$\{p,q,z\}$ is a blocker. The pair $X$ row is private for $p$, because
$z\ne u$. The pair $Y$ row is private for $q$, because its second point lies
outside $N$. The row $N$ is private for $z$. This blocker lies outside both
families in (13), raising the total from at least five to at least six.

The four values of $c$ exhaust all distributions. This proves (11).

## Consequences

In the $c=1$ branch of the five-row pair-blocker argument, Lemma 1 replaces
the 294-vector four-row table. The retained residual triples $P,Q$ intersect
in one point, while Lemma 1 forces intersection two.

In the $c=2$ branch, apply Lemma 2 to

$$
\mathcal H=\mathcal R.
$$

Every row of $\mathcal R$ has size at least two, at most three are pairs, and
every row of $B(\mathcal R)=\mathcal T$ has size at least three. Thus
$\tau(\mathcal R)\ge3$. Private rows give $|\mathcal R|\ge3$, while the
residual construction gives $|\mathcal R|\le5$. Lemma 2 now gives
$|\mathcal T|\ge6$. This replaces both the four-row and five-row residual
enumerations in that branch.

The G4.12 artifacts, claim files, and status files remain unchanged.
