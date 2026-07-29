# P0054 G4.13 scratch: pair-endpoint saturation

```text
STATUS: PROVED_CANDIDATE
SCOPE: FIVE_ROW_KERNEL_COMPLETION_IN_THE_G4_12_(8,8)_BRANCH
RESULT: REMOVE_THE_FOUR_LOW_DUAL_DEGREE_CLASSES
NETWORK: MATHEMATICS_OFFLINE
```

All clutters below are finite. A blocker is an inclusion-minimal transversal.

## Pair-endpoint lemma

Let $\mathcal H$ be a clutter such that:

- $|\mathcal H|\ge6$;
- every row has size at least two;
- at most three rows are pairs;
- $\tau(\mathcal H)\ge3$;
- every point has $\mathcal H$-degree at most three.

If a pair row $\{p,q\}\in\mathcal H$ has both endpoint degrees at most two,
then

$$
|B(\mathcal H)|\ge6.
$$

In particular, if $|B(\mathcal H)|=5$, every pair row has an endpoint of
degree three.

### Residual split

Assume for contradiction that

$$
\begin{aligned}
  d_{\mathcal H}(p) & \le2 \\
  d_{\mathcal H}(q) & \le2
\end{aligned}
\tag{1}
$$

No row other than $\{p,q\}$ contains both endpoints. Partition the remaining
rows into:

- $\mathcal X$: rows containing $p$;
- $\mathcal Y$: rows containing $q$;
- $\mathcal Z$: rows containing neither endpoint.

Equation (1) gives

$$
\begin{aligned}
  |\mathcal X| & \le1 \\
  |\mathcal Y| & \le1 \\
  |\mathcal Z| & \ge3
\end{aligned}
\tag{2}
$$

Delete the fixed endpoint and minimize:

$$
\begin{aligned}
  \mathcal L_p & =
  \min\left(
    \{Y\setminus\{q\}:Y\in\mathcal Y\}
    \cup\mathcal Z
  \right) \\
  \mathcal L_q & =
  \min\left(
    \{X\setminus\{p\}:X\in\mathcal X\}
    \cup\mathcal Z
  \right)
\end{aligned}
\tag{3}
$$

Every $D\in B(\mathcal L_p)$ gives the blocker $D\cup\{p\}$ of
$\mathcal H$. The pair row is private for $p$, and the residual private rows
remain private for the points of $D$. The analogous construction using $q$
is disjoint. Therefore

$$
|B(\mathcal H)|
\ge
|B(\mathcal L_p)|+|B(\mathcal L_q)|.
\tag{4}
$$

Neither residual blocker has a singleton row. A singleton transversal of
$\mathcal L_p$, together with $p$, would be a two-point transversal of
$\mathcal H$. The same holds with $p,q$ exchanged.

Each residual clutter has at most one singleton row, since only the
endpoint-deleted row can be a singleton. If a residual had one blocker
$Q$, blocker involution would make its minimal rows the singleton rows
$\{z\}$ for $z\in Q$. The absence of singleton blockers gives $|Q|\ge2$,
contradicting the one-singleton-row limit. Hence

$$
\begin{aligned}
  |B(\mathcal L_p)| & \ge2 \\
  |B(\mathcal L_q)| & \ge2
\end{aligned}
\tag{5}
$$

### One empty side

First suppose $\mathcal Y=\varnothing$ and
$\mathcal X=\{X\}$. Then $\mathcal L_p=\mathcal Z$. If
$|B(\mathcal Z)|\le2$, blocker involution reconstructs either a singleton
row or at least four pair rows. Both are impossible. Thus

$$
|B(\mathcal L_p)|\ge3.
\tag{6}
$$

Suppose $|B(\mathcal L_q)|=2$. Let its two blockers be $Q_1,Q_2$. If they
are disjoint, involution reconstructs at least four pair rows. The residual
has at most three possible pair rows: $X\setminus\{p\}$ and the two pair
rows still allowed in $\mathcal Z$. Therefore $Q_1,Q_2$ intersect.

Their intersection reconstructs a singleton row. It must be

$$
X\setminus\{p\}=\{w\},
\tag{7}
$$

so $X=\{p,w\}$ is a pair row. The remaining pair budget allows at most one
pair row $A\in\mathcal Z$. Involution now forces exactly one such row, and
every other row of $\mathcal Z$ contains $w$. Consequently

$$
d_{\mathcal H}(w)
\ge
1+|\mathcal Z|-1
=|\mathcal Z|.
\tag{8}
$$

Here $|\mathcal Z|\ge4$, since the rows are
$\{p,q\}$, $X$, and $\mathcal Z$. Equation (8) contradicts the degree-three
bound. Hence $|B(\mathcal L_q)|\ge3$. Equations (4) and (6) give
$|B(\mathcal H)|\ge6$.

The case $\mathcal X=\varnothing$, $\mathcal Y\ne\varnothing$ is symmetric.
If both sides are empty, the two residuals both equal $\mathcal Z$ and
equation (6) applies twice.

### Two nonempty sides

It remains that

$$
\begin{aligned}
  \mathcal X & =\{X\} \\
  \mathcal Y & =\{Y\}
\end{aligned}
\tag{9}
$$

If both residual blocker counts are at least three, equation (4) finishes
the proof. Exchange $p,q$ if needed, and suppose

$$
|B(\mathcal L_p)|=2.
\tag{10}
$$

The two-blocker involution argument used above gives:

- $Y=\{q,w\}$ is a pair row;
- $\mathcal Z$ has a unique pair row $A$;
- every row of $\mathcal Z\setminus\{A\}$ contains $w$.

Therefore

$$
d_{\mathcal H}(w)\ge|\mathcal Z|.
\tag{11}
$$

Equations (2) and (11), together with the degree-three bound, force

$$
|\mathcal Z|=3.
\tag{12}
$$

Write

$$
\mathcal Z=\{A,Z_1,Z_2\}.
\tag{13}
$$

The rows $\{p,q\}$, $Y$, and $A$ exhaust the pair budget, so $X$ is not a
pair. Thus $\mathcal L_q$ has no singleton row. It has at most two pair rows:
$A$, and possibly $X\setminus\{p\}$. If it had two blockers, involution
would reconstruct at least four pair rows. Hence

$$
|B(\mathcal L_q)|\ge3.
\tag{14}
$$

The case $|B(\mathcal L_q)|\ge4$ follows from (4). Assume the remaining
equality case:

$$
|B(\mathcal L_q)|=3.
\tag{15}
$$

Neither $Z_1$ nor $Z_2$ disappears during the minimization in (3). If both
disappeared, $\mathcal L_q$ would consist of two rows and have at least four
blockers. If exactly one disappeared, $\mathcal L_q$ would have three rows.
The exact three-row formula says that three rows of size at least two, with
three blockers and no singleton blocker, must all be pairs. The retained
large row $Z_i$ contradicts this.

Here $A$ and $X\setminus\{p\}$ necessarily survive. A containment between
them would lift to a containment between $A$ and $X$ in $\mathcal H$.
Likewise, an original row in $\mathcal Z$ cannot be contained in
$X\setminus\{p\}$; only the reverse containment can remove it.

Put

$$
\mathcal T=B(\mathcal L_q).
\tag{16}
$$

The clutter $\mathcal T$ has three rows, while
$B(\mathcal T)=\mathcal L_q$ has four rows. The row $A$ is a pair, the rows
$Z_1,Z_2$ are triples, and $X\setminus\{p\}$ is either a pair or a triple.

For completeness, apply the exact three-row partition to $\mathcal T$.
Let $a,b,c$ be the private multiplicities and $u,v,w'$ the three pairwise
multiplicities. The triple intersection is empty because
$B(\mathcal T)$ has no singleton row. The numbers of pair and triple
blockers are:

$$
\begin{aligned}
  P & =uv+uw'+vw'+uc+vb+w'a \\
  R & =abc
\end{aligned}
\tag{17}
$$

Here $P+R=4$, $1\le P\le2$, and $R\ge2$. If $P=1$, then $R=3$, so the
private multiplicities are $1,1,3$ up to permutation. The two rows with one
private point need pairwise-support points. A point shared by those two rows
contributes at least three to $P$; using two different shared classes also
contributes at least three. Thus $P=1$ is impossible. Hence

$$
\begin{aligned}
  P & =2 \\
  R & =2
\end{aligned}
\tag{18}
$$

After permuting the three rows, put $(a,b,c)=(1,1,2)$. The first two rows
need $u+v\ge1$ and $u+w'\ge1$. If $u=0$, then $v,w'\ge1$ and (17) gives
$P\ge3$. Thus $u\ge1$. The term $uc$ already equals at least two, so equality
in (18) forces

$$
(a,b,c,u,v,w')=(1,1,2,1,0,0).
\tag{19}
$$

Thus there are distinct points $r_1,r_2,s,t,c_0$ such that

$$
\begin{aligned}
  A & =\{c_0,r_1\} \\
  X\setminus\{p\} & =\{c_0,r_2\} \\
  Z_1 & =\{s,t,r_1\} \\
  Z_2 & =\{s,t,r_2\}
\end{aligned}
\tag{20}
$$

Both $Z_1,Z_2$ contain the point $w$ from (10), so exchange $s,t$ if
needed and put $s=w$. The set

$$
\{p,q,t,r_1\}
\tag{21}
$$

is now a blocker of $\mathcal H$. It hits $X$ through $p$, $Y$ through $q$,
$A$ through $r_1$, and $Z_1,Z_2$ through $t$. These four rows are private
for the four selected points, respectively. The blocker in (21) contains
both $p,q$, so it lies outside both injected families in (4).

Equations (4), (10), (14), (15), and (21) give

$$
|B(\mathcal H)|\ge2+3+1=6.
\tag{22}
$$

This proves that two low-degree endpoints force at least six blockers. The
five-row dual in the intended application has exactly five rows, so the
stated corollary follows.

## Application to the five-row kernel

Let $\mathcal K$ be the five-row kernel in the degree-three branch of the
G4.12 $(8,8)$ split, and put

$$
\mathcal H=B(\mathcal K).
\tag{23}
$$

Blocker involution gives $B(\mathcal H)=\mathcal K$, so
$|B(\mathcal H)|=5$.

The companion pair-blocker lemma gives exactly three pair rows in
$\mathcal H$. Suppose the forced base obtained by adding the external point
to those pairs has maximum degree at most three. Then $\Delta(\mathcal H)\le3$.

If $|\mathcal H|\in\{6,7\}$, every pair row has an endpoint of
$\mathcal H$-degree three. Any additional row must contain a pair row by the
completion lemma. It raises that endpoint to degree four. Hence no additional
row exists.

This removes the four low-dual-degree canonical classes and all
blocker-endpoint checks from the proof. A finite certificate is still needed
only for the remaining assertion:

$$
|\mathcal H|=8
\implies
\Delta(\mathcal H)\ge4.
\tag{24}
$$

The old 24-class table and the low-dual-degree generator remain independent
`COMPUTED` cross-checks. They are no longer proof dependencies for the
$|\mathcal H|\in\{6,7\}$ completion branches.

## Degree-bound sharpness

The maximum-degree hypothesis cannot simply be deleted. On the points
$p,q,0,1,2,3,4$, take:

$$
\begin{aligned}
\mathcal H=\{&
\{p,q\},
\{q,1\},
\{0,3\},
\{1,2,3\},\\
&
\{1,2,4\},
\{p,0,4\},
\{0,1,4\}
\}
\end{aligned}
\tag{25}
$$

This clutter has three pair rows, transversal number three, and the pair
$\{p,q\}$ has both endpoint degrees two. Its blocker has five rows, while
point $1$ has $\mathcal H$-degree four. Thus the proof uses the inherited
degree-three bound at the exact place where it is needed.
