# P0054 G4.9 candidate: the middle layer has at least fourteen members

```text
CURRENT_GATE: P0054_G4_9_MIDDLE_LAYER_TOTAL_THIRTEEN
LOCAL_TARGET: m(3,3) >= 14
CANDIDATE_CONCLUSION: sat(7) >= 52
STATUS: PROVED_CANDIDATE_PENDING_REFEREE
```

## 1. Statement and reduction

`PROVED` relative to the frozen G4.8 inputs: let $S$ and $C$ be finite
clutters on an arbitrary finite ground set such that

$$
S=B(C),\qquad C=B(S)
$$

and every member of $S\cup C$ has size at least three. Then

$$
|S|+|C|\ge14 \tag{1.1}
$$

The accepted G4.8 proof gives the lower bound thirteen. If equality held,
exchange the two sides so that $|S|\le|C|$. The frozen split classification
leaves only

$$
(|S|,|C|)\in\{(4,9),(5,8),(6,7)\} \tag{1.2}
$$

Sections 3, 4, and 5 exclude these splits separately.

## 2. Auxiliary blocker lemmas

### Lemma 2.1: exact three-row equality information

`PROVED`: let $K=\{A,B,C\}$ be a three-row clutter. Suppose every row has
size at least three and $\tau(K)\ge2$. If $|B(K)|=7$, at most one member of
$B(K)$ has size at least three.

### Proof

The triple intersection is empty. Partition the active ground set into the
three private classes and the three pairwise-intersection classes. Write

$$
\begin{aligned}
  p & =|A\setminus(B\cup C)|, & q & =|B\setminus(A\cup C)|, & r & =|C\setminus(A\cup B)|, \\
  x & =|A\cap B|, & y & =|A\cap C|, & z & =|B\cap C|
\end{aligned}
$$

Every minimal transversal is either a two-point transversal from two suitable
incidence classes or a triple containing one private point of each row. Hence

$$
|B(K)|=xy+xz+yz+xr+yq+zp+pqr \tag{2.1}
$$

The size-three blockers are exactly the $pqr$ private triples. Suppose
$pqr\ge2$. If none of $x,y,z$ is positive, the row-size constraints give
$p,q,r\ge3$, so (2.1) is at least $27$.

If exactly one is positive, say $x>0$, then $r\ge3$ and

$$
|B(K)|=r(x+pq)\ge9
$$

Indeed, $x=1$ forces $p,q\ge2$; $x=2$ forces $p,q\ge1$; and $x\ge3$ is
larger still.

If exactly two are positive, say $x,y>0$, the relevant part of (2.1) is

$$
xy+xr+yq+pqr
$$

For $(x,y)=(1,1)$, the row-size constraints give $q,r\ge2$, and the expression
is at least $9$. If exactly one of $x,y$ is $1$, the row using only that
intersection needs at least two private points, and the expression is again at
least $9$. If $x,y\ge2$, it is at least $10$.

If all three are positive, then

$$
xy+xz+yz\ge3,\qquad xr+yq+zp\ge p+q+r\ge4
$$

Together with $pqr\ge2$, this again gives at least $9$. Thus $|B(K)|=7$
forces $pqr\le1$. This proves the lemma. $\square$

### Lemma 2.2: one residual row cannot collapse the blocker count

`PROVED`: let $D$ be a nonempty finite clutter whose rows have size at least
three. Let $P_1,\dots,P_t$ be additional nonempty sets, and let

$$
L=\min\left(D\cup\{P_1,\dots,P_t\}\right)
$$

where $\min$ keeps the inclusion-minimal rows. Suppose every member of $B(L)$
has size at least two.

1. If $t\le1$, then $|B(L)|\ge3$.
2. If $t\le2$ and every $P_i$ has size at least two, then $|B(L)|\ge2$.

### Proof

If $B(L)=\{Q\}$, blocker involution makes $L$ the family of singleton rows
$\{\{q\}:q\in Q\}$. Since $|Q|\ge2$, this produces at least two singleton
rows. It contradicts the first claim because at most one input row can have
size below three. It contradicts the second claim because no input row is a
singleton.

For the first claim, suppose instead that $B(L)=\{Q_1,Q_2\}$. The two rows
are incomparable and have size at least two. Blocker involution says that $L$
contains

- one singleton $\{u\}$ for every $u\in Q_1\cap Q_2$;
- one pair $\{v,w\}$ for every
  $(v,w)\in(Q_1\setminus Q_2)\times(Q_2\setminus Q_1)$.

If the two rows intersect, this list has at least one singleton and one pair.
If they are disjoint, it has at least four pairs. Thus $L$ has at least two
rows of size at most two. Only the single added row $P_1$ could supply such a
row, a contradiction. $\square$

## 3. The four-nine split

### Lemma 3.1

`PROVED`: let $H$ be a four-row clutter whose rows have size at least three
and whose transversal number is at least three. Then

$$
|B(H)|\ge19 \tag{3.1}
$$

### Proof

Let $J$ be the intersection graph of the four rows. Two vertex-disjoint edges
of $J$ would supply two points covering all four rows. Hence $\nu(J)\le1$.

If $J$ has at least two isolated vertices, blocker factorization across its
disjoint components applies. An isolated row contributes at least three
choices. For a possible two-row component $\{A,B\}$, put

$$
i=|A\cap B|,\qquad p=|A\setminus B|,\qquad q=|B\setminus A|
$$

The clutter and row-size conditions give

$$
|B(\{A,B\})|=i+pq\ge3
$$

Thus this case has at least $3\cdot3\cdot3=27$ blockers.

If $J$ has exactly one isolated row $E$, let $K$ be the other three rows.
Then $\tau(H)=1+\tau(K)$, so $\tau(K)\ge2$. The accepted G4.8 three-row
lemma gives $|B(K)|\ge7$. Factorization yields

$$
|B(H)|=|E||B(K)|\ge3\cdot7=21
$$

It remains that $J$ has no isolated vertex. Every two edges of $J$ intersect,
so $J$ is a three-leaf star. Let $C$ be its center and let $L_1,L_2,L_3$ be
its leaves. Put

$$
X_i=C\cap L_i,\qquad Y_i=L_i\setminus C,\qquad
Z=C\setminus(L_1\cup L_2\cup L_3)
$$

Write $x_i=|X_i|$, $y_i=|Y_i|$, $z=|Z|$, and $n_i=x_i+y_i$. The clutter
condition gives $x_i,y_i\ge1$, while $n_i\ge3$.

Every minimal transversal is exactly one of the following:

- one point from each $L_i$, with at least one selected point in an $X_i$;
- one point from each $Y_i$, together with one point of $Z$.

Therefore

$$
|B(H)|=n_1n_2n_3+(z-1)y_1y_2y_3 \tag{3.2}
$$

If $z\ge1$, this is at least $27$. If $z=0$, then $y_i\le n_i-1$, so

$$
|B(H)|\ge n_1n_2n_3-(n_1-1)(n_2-1)(n_3-1)\ge19
$$

The final expression increases in each $n_i\ge3$ and equals $19$ at
$n_1=n_2=n_3=3$. This proves (3.1). $\square$

`PROVED`: the bound is sharp. Take

$$
C=\{x_1,x_2,x_3\},\qquad L_i=\{x_i,a_i,b_i\}
$$

The blockers are the $27-8=19$ triples that choose one point from each leaf
without choosing all three private points.

## 4. The five-eight split

### Lemma 4.1

`PROVED`: let $H$ be a five-row clutter whose rows have size at least three
and whose transversal number is at least three. Then

$$
|B(H)|\ge9 \tag{4.1}
$$

### Proof

We strengthen only the tight branch of the accepted G4.8 five-row proof. For
any point $e$, delete $e$ from every row of $H$, keep the inclusion-minimal
residual rows in $R$, and put $T=B(R)$. Every row of $R$ has size at least
two, and $|R|\le5$. The members of $T$ are exactly the blockers of $H$ that
avoid $e$, so every one has size at least three. Blocker involution gives
$R=B(T)$.

We claim $|T|\ge4$. One member would make $R$ a family of singleton rows. For
two members, an intersection creates a singleton row in $R$, while disjoint
members create at least $3\cdot3=9$ rows. If $|T|=3$, then $\tau(T)\ge2$
because every row of $R$ has size at least two. The accepted G4.8 three-row
lemma gives

$$
|R|=|B(T)|\ge7
$$

Each case contradicts the properties of $R$. Hence at least four blockers of
$H$ avoid $e$.

In the only formerly tight matching branch, two actual matchings share an
actual point:

$$
M=\{e,f\},\qquad N=\{e,g\}
$$

The accepted G4.8 generated families give at least six blockers containing
$e$ when $f$ and $g$ are parallel actual points. Otherwise they give at least
five, because their only possible common member is $\{e,f,g\}$. The four
blockers avoiding $e$ are outside both generated families. These cases give
at least ten and nine blockers, respectively. Every other branch already
gives at least nine in the accepted G4.8 proof. This proves (4.1). $\square$

## 5. The six-seven split

### Lemma 5.1

`PROVED`: let $H$ be a six-row clutter whose rows have size at least three
and whose transversal number is at least three. Then

$$
|B(H)|\ge8 \tag{5.1}
$$

### Proof: points of high incidence

The accepted G4.8 proof gives at least nine blockers when a point belongs to
at least four rows. Suppose a point $x$ belongs to exactly three rows, and let
$K$ be the other three rows. Then $\tau(K)\ge2$. For every $T\in B(K)$, use
$T$ if it hits all six rows and use $T\cup\{x\}$ otherwise. Private rows in
$K$, together with a row missed by $T$ in the second case, show that this is
an injection

$$
B(K)\hookrightarrow B(H) \tag{5.2}
$$

The accepted three-row lemma gives $|B(K)|\ge7$. If it is at least eight, we
are done. Suppose $|B(K)|=7$. By Lemma 2.1, at most one member of $B(K)$ has
size at least three.

Now delete $x$ from every row of $H$ and keep the inclusion-minimal residual
rows in $R$. Every row of $R$ has size at least two. Hence $B(R)$ has at least
two members: one member would make $R$ a family of singleton rows. The members
of $B(R)$ are exactly the blockers of $H$ that avoid $x$.

An image member in (5.2) that avoids $x$ is a member $T\in B(K)$ that is also
a blocker of $H$. It therefore has size at least three. Lemma 2.1 shows that
at most one of the seven image members avoids $x$. Since $H$ has at least two
blockers avoiding $x$, one lies outside the image. Thus $|B(H)|\ge8$.

We may therefore assume every active point belongs to at most two rows. As in
G4.8, represent points by actual loops and nonloop edges on the six row
indices, retaining parallel actual points. The accepted matching-number zero,
one, and two branches each give at least nine blockers. It remains to treat an
actual perfect matching.

### Proof: an actual perfect matching

Fix an actual perfect matching

$$
M=\{e_1,e_2,e_3\}
$$

It is a three-point blocker of $H$. Delete its three points from the rows of
$H$ and keep the inclusion-minimal residual rows in $R$. Every row of $R$ has
size at least two. Put $D=B(R)$. The rows of $D$ are exactly the blockers of
$H$ that avoid $M$, and each has size at least three.

The accepted G4.8 argument gives $|D|\ge4$. For completeness, one member would
make $R$ contain singleton rows. Two members either create a singleton row or
at least $3\cdot3=9$ rows. Three members have transversal number at least two,
so the G4.8 three-row lemma gives $|R|\ge7$. All alternatives contradict the
six residual rows of size at least two.

Suppose for contradiction that $|B(H)|\le7$, and put $C=B(H)$. Besides $M$
and the rows of $D$, the clutter $C$ has at most two rows $N_1,\dots,N_s$ that
meet $M$, where $s\le2$. Write

$$
I_j=N_j\cap M,\qquad P_j=N_j\setminus M
$$

Each $I_j$ is a nonempty proper subset of $M$, and each $P_j$ is nonempty,
since $C$ is a clutter. For each $e\in M$, define

$$
L_e=\min\left(D\cup\{P_j:e\notin I_j\}\right)
$$

Every $Q\in B(L_e)$ gives a blocker $\{e\}\cup Q$ of $C$. The row $M$ is
private for $e$. A private row for a point of $Q$ is either a row of $D$ or an
uncovered $N_j$, so minimality is preserved. These blockers have exactly one
point of $M$, and blockers constructed from different $e$ are distinct.
Moreover, $B(C)=H$ and every row of $H$ has size at least three. Thus every
$Q\in B(L_e)$ has size at least two.

If $s\le1$, every $L_e$ adds at most one residual row to $D$. Lemma 2.2 gives
at least three blockers for each $e$, hence at least nine members of $B(C)$.

Suppose $s=2$. If $|I_1\cup I_2|\ge2$, each point in this union leaves at most
one residual row uncovered. It contributes at least three blockers by Lemma
2.2. A possible third point contributes at least one. Hence $|B(C)|\ge7$.

The only remaining case is

$$
I_1=I_2=\{e_0\}
$$

Both $P_1$ and $P_2$ have size at least two because the rows $N_1,N_2$ have
size at least three. The point $e_0$ contributes at least three blockers by
the first part of Lemma 2.2. Each of the other two points leaves both residual
rows uncovered and contributes at least two blockers by the second part.
Thus again

$$
|B(C)|\ge3+2+2=7
$$

But blocker involution gives $B(C)=H$, which has exactly six rows. This
contradiction proves (5.1). $\square$

## 6. Local and global deductions

`PROVED` relative to the frozen inputs: assume equality in the accepted G4.8
lower bound and orient the two sides as
in (1.2).

- If $|S|=4$, Lemma 3.1 gives $|C|\ge19$.
- If $|S|=5$, Lemma 4.1 gives $|C|\ge9$.
- If $|S|=6$, Lemma 5.1 gives $|C|\ge8$.

Every case contradicts $|S|+|C|=13$. This proves (1.1). Applying it to the
accepted middle-layer interface gives

$$
|A_3|\ge14
$$

Together with the frozen other-layer bounds, this yields

$$
|F|\ge1+6+12+14+12+6+1=52 \tag{6.1}
$$

Thus the frozen eventual-stability reduction gives the candidate consequence
$\operatorname{sat}(7)\ge52$.

## 7. Evidence boundary

`PROVED_CANDIDATE_PENDING_REFEREE`: the proof is combinatorial and works on an
arbitrary finite ground set. Inactive points never enter a minimal
transversal. Incidence-class counts retain parallel actual points. The use of
inclusion-minimal residual rows covers repeated residual supports, nonuniform
row sizes, loops, and empty optional incidence classes. Blocker involution
preserves both orientations.

`UNKNOWN`: exact $m(3,3)$, exact $\operatorname{sat}(7)$, novelty, and priority.

No claim or status file is modified by this candidate.
