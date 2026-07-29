# P0054 G4.13 scratch: pure `P4` eight-blocker obstruction

```text
STATUS: PROVED_CANDIDATE
SCOPE: EIGHT_BLOCKERS_WITH_P4_PAIR_GRAPH
RESULT: MAXIMUM_DUAL_DEGREE_AT_LEAST_4
NETWORK: MATHEMATICS_OFFLINE
```

All clutters below are finite. A blocker is an inclusion-minimal transversal.

## Generalized three-row trace lemma

Let $a,b$ be distinct points, and let $C,E$ be two-point sets such that
$a\notin E$ and $b\notin C$. Let
$\mathcal Z=\{Z_1,Z_2,Z_3\}$ be a three-row clutter. Assume:

- every row has size at least three;
- every row contains $b$ or all of $C$;
- every row contains $a$ or all of $E$;
- for every $x\in\{a,b\}\cup C\cup E$,

$$
d_{\mathcal Z}(x)
+\mathbf 1_{x=a}
+\mathbf 1_{x=b}
+\mathbf 1_{x\in C}
+\mathbf 1_{x\in E}
\le3.
\tag{1}
$$

Call $T\in B(\mathcal Z)$ good when:

$$
\begin{aligned}
  a\in T &\implies T\cap E=\varnothing, \\
  b\in T &\implies T\cap C=\varnothing.
\end{aligned}
\tag{2}
$$

Then $B(\mathcal Z)$ contains at least two good rows.

### No endpoint identifications

First suppose $a\notin C$, $b\notin E$, and $C\cap E=\varnothing$. Write
$C=\{c,d\}$ and $E=\{e,f\}$. All six displayed points are distinct, and
each occurs in at most two rows of $\mathcal Z$.

Every row contains one of the four traces:

$$
\begin{aligned}
  A&=\{a,b\}, & C'&=\{a,c,d\}, \\
  E'&=\{b,e,f\}, & N&=\{c,d,e,f\}.
\end{aligned}
\tag{3}
$$

Choose one contained trace for each row. The degree bounds exclude a triple
in which a fixed point occurs three times. Up to exchanging the two sides,
exchanging the points inside $C$ or $E$, and permuting the rows, the possible
trace triples have the following good transversals:

| Trace triple | Two good transversals |
|---|---|
| $A,A,N$ | $\{a,c\},\{a,d\}$ |
| $A,C',N$ | $\{a,c\},\{a,d\}$ |
| $A,E',N$ | $\{b,e\},\{b,f\}$ |
| $A,N,N$ | $\{a,c\},\{a,d\}$ |
| $C',C',E'$ | $\{a,b\},\{c,e\}$ |
| $C',E',E'$ | $\{a,b\},\{c,e\}$ |
| $C',E',N$ | $\{c,e\},\{c,f\}$ |

Minimizing the displayed transversals inside the original rows preserves
goodness. Their intersections are empty or a singleton fixed point. Such a
singleton cannot hit all three rows by (1), so the resulting blockers remain
distinct.

The omitted triple is $A,C',E'$. It has the good blocker $\{a,b\}$. The row
containing $A$ has a third point $z$. If $z\in C$, use $\{z,e\}$; if
$z\in E$, use $\{c,z\}$. Otherwise use, according to the support of $z$ on
the three rows,

$$
\{z\},\ \{z,b\},\ \{z,a\},\ \text{or }\{z,c,e\}.
\tag{4}
$$

These four choices correspond respectively to support on all three rows,
on the $A,C'$ rows, on the $A,E'$ rows, or only on the $A$ row. Each is good
and does not contain both $a,b$, so its minimized blocker differs from
$\{a,b\}$.

### One endpoint lies in its opposite pair

Suppose $a\in C$; the case $b\in E$ is symmetric. Write $C=\{a,d\}$.
Condition (1) lets $a$ occur in at most one row of $\mathcal Z$. Hence at
least two rows avoid $a$ and contain all of $E$.

The cases $b\in E$ and $C\cap E\ne\varnothing$ are impossible. In the first,
those two rows both contain $b$, although (1) lets $b$ occur only once. In
the second, a point of $C\cap E$ occurs once in each of the two fixed outside
rows and then in both $a$-avoiding rows.

Thus $b\notin E$ and $C\cap E=\varnothing$. Write $E=\{e,f\}$. The two
$a$-avoiding rows contain $b,e,f$. These three points exhaust their remaining
degree budget there, so the third row contains none of them. It must contain
$a,d$, and it has a point $z\notin\{a,d\}$ because its size is at least
three. The three good transversals

$$
\{d,e\},\ \{d,f\},\ \{b,z\}
\tag{5}
$$

minimize to at least two distinct blockers. The first two can merge only to
the singleton $\{d\}$, while the third does not contain $d$.

### The two pairs overlap

It remains that $a\notin C$, $b\notin E$, and $C\cap E\ne\varnothing$.

Suppose first that $C\cap E=\{r\}$. Write $C=\{r,c\}$ and $E=\{r,e\}$.
Condition (1) lets $r$ occur in at most one row. Therefore exactly one row
$Z_a$ avoids $a$, and exactly one row $Z_b$ avoids $b$.

If $b\in Z_a$, put $T_a=\{a,b\}$; otherwise $C\subseteq Z_a$ and put
$T_a=\{a,c\}$. If $a\in Z_b$, put $T_b=\{a,b\}$; otherwise
$E\subseteq Z_b$ and put $T_b=\{b,e\}$. Both are good transversals.
They cannot both equal $\{a,b\}$: then the distinct rows $Z_a,Z_b$ would
both contain $r$, contrary to its degree bound. Otherwise their intersection
is empty or is the singleton $a$ or $b$, neither of which hits all three
rows. Their minimized blockers are distinct.

Finally suppose $C=E=\{c,d\}$. Each of $c,d$ occurs in at most one row.
There is a unique row $Z_a$ avoiding $a$ and a unique row $Z_b$ avoiding
$b$. If $b\in Z_a$, put $T_a=\{a,b\}$; otherwise choose
$z_a\in Z_a\setminus C$ and put $T_a=\{a,z_a\}$. Define $T_b$ symmetrically.
These are good transversals.

Their minimizations are distinct unless $Z_a=Z_b=:Z_0$, the two chosen
points agree as $z$, and $z$ lies in all three rows. If
$Z_0\setminus(C\cup\{z\})$ is nonempty, a point $w$ there makes
$\{a,w\}$ a good transversal avoiding $z$. Otherwise
$Z_0=C\cup\{z\}$. The other two rows contain $a,b,z$ and are incomparable,
so choose points

$$
x\in Z_1\setminus Z_2,\ y\in Z_2\setminus Z_1.
\tag{6}
$$

Neither point lies in $C$, whose degree budget was exhausted in $Z_0$.
Then $\{c,x,y\}$ is a good transversal avoiding $z$. This again gives a
second blocker. The generalized trace lemma follows.

## Pair-graph lemma

Let $\mathcal H$ be a clutter such that:

- $|\mathcal H|=8$;
- exactly three rows are pairs and their graph is a path with three edges;
- every other row has size at least three;
- $|B(\mathcal H)|=5$ and every blocker has size at least three;
- every point has degree at most three in both $\mathcal H$ and
  $B(\mathcal H)$.

These assumptions are inconsistent.

Label the pair path:

$$
\{a,p\},\ \{p,q\},\ \{q,b\}.
\tag{7}
$$

### Dual supports of the central pair

For a point $x$, let $S_x$ be the set of rows of $B(\mathcal H)$ containing
$x$. A pair row is a minimal transversal of the five-row dual. Hence the
supports of its endpoints cover all five rows, and each endpoint has a
private row. Every support has size at most three.

If $|S_p|=2$, the edge $\{p,q\}$ forces $S_q$ to be the complementary
three-set. The edge $\{a,p\}$ then forces $S_a=S_q$. Since
$\{q,b\}$ is minimal, $S_b$ contains the two-set $S_p$ and omits at least
one point of $S_q$. Thus $S_a\cup S_b$ covers all five rows, with a private
row on each side. This would make $\{a,b\}$ a fourth pair row. Therefore
$|S_p|=3$, and symmetrically $|S_q|=3$.

The two central supports cover five rows and meet in one. Consequently there
are exactly two dual rows containing $p$ but not $q$, and exactly two
containing $q$ but not $p$.

### Residual involution

Apply the five-blocker corollary of
`/private/tmp/p0054_g413_pair_endpoint_lemma_v2.md` to $\{p,q\}$. Exchange
the two sides if needed and put $d_{\mathcal H}(p)=3$. Besides the two pair
rows through $p$, there is one nonpair row $X$ containing $p$.

Form the residual clutter from the five rows avoiding $p$, deleting $q$ from
every such row and then minimizing. Its blocker consists exactly of the two
sets obtained by deleting $p$ from the dual rows containing $p$ but not $q$.
Both have size at least two.

If $d_{\mathcal H}(q)=2$, the residual sources are the singleton $\{b\}$
and four rows of size at least three. A clutter with two blockers necessarily
has a pair source by blocker involution, a contradiction. Hence
$d_{\mathcal H}(q)=3$.

Write the additional row through $q$ as $Y$. The residual sources are now
$\{b\}$, $Y\setminus\{q\}$, and three large rows avoiding $p,q$.
Two-blocker involution forces distinct points $c,d$ such that

$$
Y=\{q,c,d\},
\tag{8}
$$

every remaining row contains $b$ or all of $C:=\{c,d\}$, and the two dual
rows containing $p$ but not $q$ are

$$
\{p,b,c\},\ \{p,b,d\}.
\tag{9}
$$

The symmetric argument gives distinct points $e,f$ such that

$$
X=\{p,e,f\},
\tag{10}
$$

every remaining row contains $a$ or all of $E:=\{e,f\}$, and the two dual
rows containing $q$ but not $p$ are

$$
\{q,a,e\},\ \{q,a,f\}.
\tag{11}
$$

The clutter property gives $a\notin E$ and $b\notin C$.

### Final two blockers

Let $\mathcal Z$ be the three rows avoiding $p,q$. For every fixed point
$x\in\{a,b\}\cup C\cup E$, the four rows in (7), (8), and (10) contribute
exactly

$$
\mathbf 1_{x=a}
+\mathbf 1_{x=b}
+\mathbf 1_{x\in C}
+\mathbf 1_{x\in E}
\tag{12}
$$

to its $\mathcal H$-degree outside $\mathcal Z$. Thus the degree-three
hypothesis gives (1), and (8), (10) give the two row-trace conditions. The
generalized trace lemma supplies two distinct good rows
$T_1,T_2\in B(\mathcal Z)$.

For each good $T$, the set $T\cup\{p,q\}$ is a blocker of $\mathcal H$.
The points of $T$ retain private rows in $\mathcal Z$. If $a\notin T$, the
pair $\{a,p\}$ is private for $p$; if $a\in T$, goodness makes $X$ private
for $p$. The analogous statement using $b,C,Y$ makes $q$ private.

These two blockers are distinct and contain both $p,q$. Together with the
four blockers in (9), (11), they give

$$
|B(\mathcal H)|\ge6,
\tag{13}
$$

contrary to the assumed five-row dual. This proves the pair-graph lemma.

## G4.12 consequence

In the eight-blocker branch of the G4.12 five-row kernel, suppose the forced
base had maximum degree at most three. Put $\mathcal H=B(\mathcal K)$. If
the three pair blockers form a path with three edges, the pair-graph lemma
applies and gives a contradiction. Therefore every `P4` kernel has a point
of blocker-side degree at least four.

This removes all seven `P4` eight-blocker canonical classes from the finite
classification dependency. The `P3+K2` and `3K2` pair graphs remain open in
the pure argument.
