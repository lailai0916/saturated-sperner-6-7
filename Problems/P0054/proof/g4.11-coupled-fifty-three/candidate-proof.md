# P0054 G4.11 candidate: the total-fifty-three profile is impossible

```text
CURRENT_GATE: P0054_G4_11_COUPLED_TOTAL_FIFTY_THREE
CANDIDATE_CONCLUSION: sat(7) >= 54
STATUS: PROVED_CANDIDATE_PENDING_REFEREE
NETWORK: MATHEMATICS_OFFLINE
```

## 1. Statement and slack reduction

`PROVED_CANDIDATE` relative to the frozen G4.11 inputs: the layer profile

$$
(|A_0|,\dots,|A_6|)=(1,6,12,15,12,6,1) \tag{1.1}
$$

is impossible in the arbitrary-finite canonical decomposition.

The accepted layer minima sum to 52. Suppose the total size is 53. If
$|A_3|=14$, the frozen G4.10 classification makes the middle blocker pair
Fano. If $|A_2|=12$, Proposition 7.3 of G4.10 excludes the lower interface.
Otherwise the unique slack member lies in $A_2$, so $|A_4|=12$, and the
complementary upper exclusion applies. Thus every remaining total-53 system
has (1.1).

Write

$$
\begin{aligned}
  \mathcal F & =S_2 & \mathcal G & =C_2 \\
  \mathcal H & =S_3 & \mathcal K & =C_3 \\
  \mathcal P & =S_4 & \mathcal Q & =C_4
\end{aligned}
$$

The lower adjacent interface is equivalent, by frozen G4.10 Section 6, to:

1. every $G\in\mathcal G$ strictly contains some $K_G\in\mathcal K$;
2. $\mathcal F\cap\mathcal H=\varnothing$.

For the upper interface, substitute

$$
(\mathcal F,\mathcal G,\mathcal H,\mathcal K)
\longmapsto
(\mathcal Q,\mathcal P,\mathcal K,\mathcal H)
$$

in the same proved equivalence. The ordered minimum row sizes remain
$(2,4,3,3)$. Hence the full upper conditions are equivalent to:

1. every $P\in\mathcal P$ strictly contains some $H_P\in\mathcal H$;
2. $\mathcal K\cap\mathcal Q=\varnothing$.

This verifies the ordered upper interface rather than invoking an unchecked
symmetry.

## 2. Blocker facts

All families below are finite clutters on one arbitrary finite $U$.

### Lemma 2.1: private rows

`PROVED` in frozen G4.10: if $T\in B(\mathcal D)$, every $x\in T$ has a
private row $D_x\in\mathcal D$ with

$$
T\cap D_x=\{x\}
$$

Distinct points have distinct private rows. Thus $|T|\le|\mathcal D|$.

### Lemma 2.2: residual blockers

`PROVED` in frozen G4.10: delete a point $x$ from every row of $\mathcal D$
and keep the inclusion-minimal residual rows in $\mathcal R$. Then
$B(\mathcal R)$ is exactly the family of blockers of $\mathcal D$ that avoid
$x$. If every residual row has size at least two, there are at least two such
blockers.

### Lemma 2.3: injection through a point

`PROVED` in frozen G4.10: let $\mathcal D_0$ be the rows of $\mathcal D$ that
avoid $x$. For every $T\in B(\mathcal D_0)$, use $T$ if it hits every row of
$\mathcal D$, and use $T\cup\{x\}$ otherwise. Private rows give an injection

$$
B(\mathcal D_0)\hookrightarrow B(\mathcal D) \tag{2.1}
$$

### Lemma 2.4: three rows

`PROVED` in frozen G4.10: let $\mathcal D_0$ have three rows, row sizes at
least three, and transversal number at least two. There is no point common to
all three rows. Let $p,q,r$ be the private incidence-class multiplicities,
and let $x,y,z$ be the three pairwise incidence-class multiplicities. Then

$$
|B(\mathcal D_0)|=b_2+b_3 \tag{2.2}
$$

where

$$
\begin{aligned}
  b_2 & =xy+xz+yz+xr+yq+zp \\
  b_3 & =pqr
\end{aligned} \tag{2.3}
$$

Here $b_2$ and $b_3$ count the pair and triple blockers, respectively.

For the middle pair, every row on each side has size at least three. Hence
both transversal numbers are at least three. Lemma 2.1 also bounds every row
size by the number of rows on the opposite side.

## 3. The split $(5,10)$

Exchange the middle sides if necessary and let $\mathcal D$ be the five-row
side. Then $|B(\mathcal D)|=10$.

No point belongs to four or five rows. Such a point can be extended with at
most one further point to a transversal of size at most two.

Suppose $x$ belongs to three rows. The two rows avoiding $x$ are disjoint;
otherwise $x$ and a common point form a two-point transversal. Choosing one
point from each of the two rows gives at least

$$
3\times3=9
$$

minimal blockers containing $x$. After deleting $x$, every residual row has
size at least two. Lemma 2.2 gives at least two blockers avoiding $x$. Thus
$|B(\mathcal D)|\ge11$, a contradiction.

Every active point therefore belongs to at most two rows. The actual points
form a loop-multigraph on the five row indices, with parallel actual points
retained. The frozen G4.10 support-multigraph reduction and exhaustive output
give at least 15 minimal edge covers. This contradicts the ten-row blocker.

Thus $(5,10)$ is impossible. Exchanging sides excludes $(10,5)$.

## 4. The split $(6,9)$

Let $\mathcal D$ be the six-row side and let $\mathcal E=B(\mathcal D)$ have
nine rows.

### Lemma 4.1: point degrees on the nine-row side

`PROVED`: every point has $\mathcal E$-degree at most five. Degree at least
eight gives a transversal of $\mathcal E$ with at most two points. At degree
seven, the two avoiding rows must be disjoint, and point choices from them
give at least nine blockers, more than the six rows of $B(\mathcal E)$.
At degree six, the three avoiding rows have at least seven blockers by
Lemma 2.4. Injection (2.1) again gives more than six blockers.

### Lemma 4.2: the unique degree-three kernel

`PROVED`: a point of $\mathcal D$-degree at least four gives at least nine
blockers containing the point and at least two residual blockers avoiding it.
Suppose instead that every point has degree at most two. Represent the active
points as actual loops and nonloop edges on the six row indices, retaining
parallel actual points. Choose an inclusion-minimal submultigraph $J$ in
which every row vertex has degree at least three. Every minimal edge cover of
$J$ has a private row for each selected actual point, so it is also a blocker
of $\mathcal D$. Inclusion-minimality also makes every point of $J$ incident
with a degree-three vertex. Let $\nu$ be the matching number of the simple
nonloop support graph of $J$.

If $\nu=0$, independent loop choices give at least $3^6$ blockers. If
$\nu=1$, fix an actual matching edge. The frozen G4.8 construction chooses
one incident actual point at each of the other four vertices and gives at
least $3^4$ distinct blockers.

Suppose $\nu=2$. Fix an actual two-edge matching $M$, and let $u,v$ be the
unmatched vertices. There is no nonloop edge between $u$ and $v$. Write
$I(t)$ for the actual points of $J$ incident with a vertex $t$, and let
$d(t)=|I(t)|$. For every pair in $I(u)\times I(v)$, minimize its union with
$M$ inside $J$. The two chosen points remain because $u$ and $v$ are private.
Different pairs give distinct blockers of $\mathcal D$. Hence there are at
least

$$
d(u)d(v)\ge9.
$$

If $d(u)\ge4$ or $d(v)\ge4$, this already gives at least 12 blockers. It
remains that $d(u)=d(v)=3$. Put

$$
S=I(u)\cup I(v)\cup M.
$$

The four matched vertices have total row degree at least 12. The two points
of $M$ contribute four incidences there. The six points in
$I(u)\cup I(v)$ contribute at most six more, because each point has degree at
most two. Thus some point $z$ of $J$ incident with a matched vertex lies
outside $S$.

Every active point of a finite clutter belongs to a minimal blocker. Indeed,
choose a row $R$ containing $z$. For every row $D$ avoiding $z$, clutter
minimality gives a point in $D\setminus R$. Adjoin one such point for each
$D$ to $z$, then minimize the resulting transversal. All added points avoid
$R$, so $z$ remains in the minimal blocker.

The first nine blockers lie inside $S$, whereas this blocker contains
$z\notin S$. Therefore the $\nu=2$ case has at least ten blockers. Finally,
if $\nu=3$, the core $J$ has an actual perfect matching. Its minimality and
degree-three incidence property place it in the frozen G4.10 six-row
enumeration, which gives at least 15 minimal edge covers and hence blockers
of $\mathcal D$. Every low-degree case contradicts $|\mathcal E|=9$. Hence a
remaining case has a point $w$ of degree three.

Let $\mathcal D_0$ be the three rows avoiding $w$. Every pair blocker of
$\mathcal D_0$ must be sent by (2.1) to $\{w\}\cup T$, because every row of
$\mathcal E$ has size at least three. Lemma 4.1 and injectivity give

$$
\begin{aligned}
  b_2 & \le5 \\
  b_2+b_3 & \le9
\end{aligned} \tag{4.1}
$$

Each row of $\mathcal D_0$ has size between three and nine, so every variable
in (2.3) lies in $\{0,\dots,9\}$. The integer classification in (4.1) has one
orbit under row permutation:

$$
\begin{aligned}
  (p,q,r;x,y,z) & =(1,2,2;1,1,0) \\
  (b_2,b_3) & =(5,4)
\end{aligned} \tag{4.2}
$$

For completeness, this follows without a finite-ground assumption. If none
of $x,y,z$ is positive, then $p,q,r\ge3$ and $b_3\ge27$. If exactly one is
positive, say $x$, then $r\ge3$, $p,q\ge2$, and either $b_2>5$ or
$b_2+b_3>9$. If exactly two are positive, say $x,y$, clutter minimality gives
$q,r\ge1$. The row-size inequalities and $b_2\le5$ force
$x=y=1$, $q=r=2$, and then $p=1$. If all three are positive, either they are
all one, which gives $b_2\ge6$, or their three pair products already sum to
at least five and the remaining row-size term makes $b_2>5$.

Name the three rows from (4.2) as

$$
\{a,u,v\},\{b_1,b_2,u\},\{c_1,c_2,v\} \tag{4.3}
$$

The five pair blockers are sent to five blockers containing $w$. The four
triple blockers all contain $a$, whether their images are $T$ or
$T\cup\{w\}$. The nine injection images exhaust $\mathcal E$. Lemma 2.2
gives a blocker avoiding $w$, which must be one of the four triple images.
Consequently $\{a,w\}$ is a minimal transversal of $\mathcal E$: a pair
image is private for $w$, and a triple image avoiding $w$ is private for
$a$. Blocker involution would put this two-point row in $\mathcal D$, a
contradiction.

Thus $(6,9)$ is impossible. Exchanging sides excludes $(9,6)$.

## 5. Point degrees in the split $(7,8)$

Let $\mathcal D$ have seven rows and $\mathcal E=B(\mathcal D)$ have eight.

### Lemma 5.1: the eight-row side has degree at most four

`PROVED`: degree at least seven gives a transversal with at most two points.
At degree six, two avoiding rows give at least nine blockers. At degree five,
the three avoiding rows have exactly seven blockers in the only possible
low-count case, including six pair blockers. Their images under (2.1) contain
the chosen point. Lemma 2.2 supplies at least two further blockers avoiding
it. This exceeds the seven rows of $B(\mathcal E)$.

### Lemma 5.2: the seven-row side has degree at most three

`PROVED`: degrees at least five are excluded as above. At degree four, the
three avoiding rows have at most eight blockers and at least six pair
blockers. All six pair images contain the chosen point, contradicting the
degree-four bound on the eight-row side from Lemma 5.1.

### Lemma 5.3: the eight-row side has degree at most three

Suppose $x$ has degree four in the eight-row side. Its four avoiding rows
form a clutter with row sizes from three through seven, transversal number at
least two, at most seven blockers, and at most three pair blockers. The last
bound follows because every pair image contains $x$, while the seven-row side
has point degree at most three.

The 41 frozen G4.10 four-row kernel classes are complete for these hypotheses.
Exactly one has at most three pair blockers:

```text
3:1,5:1,6:1,9:1,10:1,12:1,|2:3|3:4
```

It is the six-edge incidence clutter of $K_4$. Its blockers are three perfect
matchings and four stars. Injection (2.1) turns the matchings into
$x$ plus a matching. They use all three allowed occurrences of $x$, so the
four stars remain unchanged. These seven rows are the Fano line clutter.
The frozen Fano self-blocking lemma gives only seven rows on the double
blocker side, not eight. This contradiction proves the lemma.

Thus every active point on both sides has degree at most three.

## 6. A three-point row

Choose a uniformly random $R\subseteq U$. Exactly one of the following
events occurs:

1. $R$ contains a row of $\mathcal D$;
2. $U\setminus R$ contains a row of $\mathcal E$.

The events are disjoint because the two families are blockers, and they are
exhaustive by blocker involution. If all 15 rows had size at least four, the
union bound would give

$$
1\le\frac{15}{16}<1
$$

Hence at least one side has a three-point row. The two possible sides require
separate reductions.

## 7. Three-point row on the eight-row side

Let $T$ be a three-point row on the eight-row side. It covers all seven rows
of the opposite side. Since every point degree is at most three, some
$x\in T$ has degree three there. Delete those three rows. The remaining
four-row kernel has:

- row sizes from three through eight;
- transversal number at least two;
- at most eight blockers and at most three pair blockers;
- point-incidence supports of rank at most three.

The first new checker exhausts all 14 nonempty rank-at-most-three supports on
four rows, all active support masks, and every actual-point multiplicity
allowed by the row-size bound. It returns one vector and one row-permutation
class:

```text
active masks:             16,383
support-feasible masks:      910
multiplicity vectors:           1
class: 3:1,5:1,6:1,9:1,10:1,12:1,|b:7|p:3
```

This is again the $K_4$ edge clutter. Its seven injection images form a Fano
line clutter on seven points. They use degree three at every Fano point, so
the eighth row $Q$ is disjoint from those points. Since $|Q|\ge3$, blocker
factorization over the two disjoint components gives

$$
7|Q|\ge21
$$

rows on the opposite side, contradicting seven.

## 8. Three-point row on the seven-row side

Let $T$ be a three-point row on the seven-row side. It covers all eight rows
of the opposite side. At least two points of $T$ have degree three; choose
one and call it $x$. Delete the three rows containing $x$. The remaining
five-row kernel has:

- row sizes from three through seven;
- transversal number at least two;
- at most seven blockers and at most three pair blockers;
- point-incidence supports of rank at most three.

The five-row checker exhausts all 25 nonempty rank-at-most-three supports.
It retains actual multiplicities rather than identifying parallel points.
Its output is:

```text
active masks:             33,554,431
support-feasible masks:       55,023
multiplicity vectors:             490
row-permutation classes:             8
```

Of the 490 vectors, 20 have six blockers and 470 have seven. Every vector has
exactly three pair blockers. There is one six-blocker class and seven
seven-blocker classes.

The support enumeration is complete. A minimal blocker uses at most five
support classes by private rows, and never uses two parallel points. Its
weighted actual count is

$$
\sum_M\prod_{s\in M}m_s
$$

where $M$ ranges over minimal support covers. Every active actual point occurs
in some blocker: choose a row containing it, choose outside points from the
other rows using the clutter condition, and minimize while keeping the chosen
row private. Thus the checker's requirement that each active support occur in
a support blocker removes no valid kernel.

For extension, each of the three pair blockers must acquire $x$. This uses
all three occurrences of $x$, so every other kernel blocker remains unchanged.
If the kernel has seven blockers, the seven-row side is determined. If it has
six, exactly one further $x$-free row $Q$ remains. New active points can occur
only in $Q$, and every multiplicity of such $Q$-private parallel points is
covered by the bound $3\le|Q|\le8$.

The extension checker reads the eight saved kernel classes. It checks the
seven determined cases and 48 admissible choices of $Q$ in the remaining
class. For each candidate it recomputes the blocker, requires exactly eight
rows, preserves the original five kernel rows, and checks all row-size and
point-degree bounds. The result is:

```text
total Q candidates: 55
valid extensions:     0
```

An independent Python verifier uses choice-union minimization rather than the
C++ powerset blocker routine. It reproduces the eight class profiles, all 55
extension candidates, zero valid extensions, the unique four-row class, and
the three labelled integer solutions in (4.2).

This excludes $(7,8)$. Exchanging the two blocker sides excludes $(8,7)$.

## 9. Global deduction and evidence boundary

Sections 3 and 4 exclude the four asymmetric outer splits. Sections 5 through
8 exclude both orientations of the remaining $(7,8)$ split. Therefore the
middle blocker pair cannot have total size 15, and profile (1.1) is
impossible.

Together with the frozen layer lower bounds and the total-53 slack reduction,
this gives the candidate consequence

$$
|F|\ge54
$$

and therefore, through the frozen eventual-stability reduction,

$$
\operatorname{sat}(7)\ge54 \tag{9.1}
$$

`COMPUTED`: the new four-row and five-row enumerations become proof
dependencies only after the arbitrary-finite reductions in Sections 7 and 8,
source audit, exact replay, and independent semantic verification. They do
not independently establish a global lower bound.

`UNKNOWN`: exact $\operatorname{sat}(7)$, novelty, priority, and a Lean
formalization of (9.1). The frozen 55-member construction still supplies the
upper bound.

No change to `claims.yaml` or `status.md` is authorized by this candidate. No
publication, expert contact, push, or G4.12 work is included.
