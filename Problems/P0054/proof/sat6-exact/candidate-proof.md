# Exact value of the saturated 6-Sperner number

```text
TARGET: sat(6)=30
STATUS: PROVED_LOCAL_CORE_FORMALIZED_EXTERNAL_REVIEW_PENDING
NETWORK: LITERATURE VERIFICATION ONLY
PUBLICATION_PRIORITY: UNKNOWN
```

## 1. Result and evidence boundary

`PROVED`: accepting the cited eventual-stability, homogeneous-atom, canonical-
decomposition, and endpoint-layer results, the argument below proves

$$
\operatorname{sat}(6)=30
$$

`LITERATURE`: Morrison, Noel, and Scott construct a saturated 6-Sperner
family of cardinality 30 on every ground set of size at least eight. This
gives the upper bound.

`PROVED`: the new lower-bound ingredient is the exact local theorem

$$
m(2,3)=9
$$

It holds on every finite trace ground set. The proof does not depend on a
bounded search.

`COMPUTED`: the companion incidence-pattern search exhausts every ordered
split of total at most eight and verifies the nine-member witness. This is
regression evidence only.

`UNKNOWN`: novelty, priority, and current publication status remain
unresolved. No statement about $\operatorname{sat}(7)=55$ follows from this
proof.

## 2. Blockers and the local parameter

Let $U$ be a finite set. A transversal of a family $\mathcal H\subseteq
\mathcal P(U)$ meets every member of $\mathcal H$. Its blocker
$B(\mathcal H)$ is the family of inclusion-minimal transversals. All
families below are clutters, meaning that no two distinct members contain
one another.

`PROVED` (finite blocker involution): for every finite clutter $\mathcal H$,

$$
B(B(\mathcal H))=\mathcal H
$$

Every $E\in\mathcal H$ meets every member of $B(\mathcal H)$, since the
latter members are transversals of $\mathcal H$. No proper subset
$D\subsetneq E$ meets every member of $B(\mathcal H)$. Indeed, the clutter
property implies that $D$ contains no member of $\mathcal H$. Thus
$U\setminus D$ meets every member of $\mathcal H$ and contains a minimal
transversal disjoint from $D$. Hence $E\in B(B(\mathcal H))$.

Conversely, suppose $D\in B(B(\mathcal H))$. If $D$ contained no member of
$\mathcal H$, then $U\setminus D$ would contain a member of
$B(\mathcal H)$ disjoint from $D$. Therefore $D$ contains some
$E\in\mathcal H$. The first direction gives $E\in B(B(\mathcal H))$, so
minimality forces $D=E$.

We use the following local parameter:

$$
\begin{aligned}
m(2,3)=\min\{&|\mathcal S|+|\mathcal C|:\mathcal S=B(\mathcal C),
\ \mathcal C=B(\mathcal S),\\
&|S|\ge2\text{ for every }S\in\mathcal S,
\ |C|\ge3\text{ for every }C\in\mathcal C\}
\end{aligned}
$$

The minimum ranges over all finite ground sets and all admissible pairs.

## 3. Private witnesses

`PROVED` (private-witness lemma): if $T\in B(\mathcal H)$ and $x\in T$,
then some $E_x\in\mathcal H$ satisfies

$$
T\cap E_x=\{x\}
$$

Minimality of $T$ says that $T\setminus\{x\}$ is not a transversal. Hence
some $E_x$ avoids $T\setminus\{x\}$. Since $T$ meets $E_x$, their
intersection is $\{x\}$.

Distinct points of $T$ have distinct private witnesses. Therefore

$$
|T|\le|\mathcal H|
$$

For an admissible pair, put $a=|\mathcal S|$ and $b=|\mathcal C|$.
Choosing one member on either side gives

$$
a\ge3,\qquad b\ge2
$$

Every transversal of $\mathcal S$ has size at least three, and every
transversal of $\mathcal C$ has size at least two. This follows because a
transversal contains a minimal transversal on a finite ground set.

## 4. Two-row and three-row lemmas

`PROVED` (two-row lemma): if $\mathcal C=\{C_1,C_2\}$, every $C_i$ has size
at least three, and $B(\mathcal C)$ has no singleton, then

$$
|B(\mathcal C)|\ge9
$$

The sets $C_1$ and $C_2$ are disjoint. Otherwise a point in their
intersection would be a singleton minimal transversal. Every choice
$x\in C_1$ and $y\in C_2$ then gives a distinct minimal transversal
$\{x,y\}$. Thus

$$
|B(\mathcal C)|=|C_1||C_2|\ge9
$$

`PROVED` (three-row lemma): let
$\mathcal C=\{C_1,C_2,C_3\}$, where every $C_i$ has size at least three. If
$B(\mathcal C)$ has no singleton, then

$$
|B(\mathcal C)|\ge7
$$

The triple intersection is empty. For $\{i,j,k\}=\{1,2,3\}$, define

$$
A_i=C_i\setminus(C_j\cup C_k),\qquad
P_i=(C_j\cap C_k)\setminus C_i
$$

Put $\alpha_i=|A_i|$ and $\pi_i=|P_i|$. These six incidence classes contain
every active point, and

$$
|C_i|=\alpha_i+\pi_j+\pi_k\ge3
$$

Every minimal transversal has size at most three. The two-element minimal
transversals are exactly the following sets:

- one point from $A_i$ and one from $P_i$;
- one point from each of $P_i$ and $P_j$, where $i\ne j$.

The three-element minimal transversals are exactly the sets with one point
from each of $A_1,A_2,A_3$. The private-witness lemma proves the forward
direction: the three witnesses must be the three distinct rows, so each
chosen point lies in only its witness row.

These classes are disjoint. Hence the exact blocker count is

$$
N=\alpha_1\alpha_2\alpha_3+
\sum_{i=1}^3\alpha_i\pi_i+
\pi_1\pi_2+\pi_1\pi_3+\pi_2\pi_3
$$

If some $\pi_i\ge2$, then the terms containing $\pi_i$ give

$$
N\ge\pi_i(\alpha_i+\pi_j+\pi_k)=\pi_i|C_i|\ge6
$$

Suppose $N=6$. By symmetry take $i=1$. Equality forces
$\pi_1=2$, $\alpha_1+\pi_2+\pi_3=3$, and

$$
\alpha_1\alpha_2\alpha_3+
\alpha_2\pi_2+\alpha_3\pi_3+\pi_2\pi_3=0
$$

Since $\pi_2\pi_3=0$, assume $\pi_2=0$ by symmetry. The row bound for
$C_3$ gives $\alpha_3\ge1$. Hence $\alpha_3\pi_3=0$ forces $\pi_3=0$.
The row bound for $C_2$ then gives $\alpha_2\ge1$, while the equality for
$C_1$ gives $\alpha_1=3$. This makes
$\alpha_1\alpha_2\alpha_3>0$, a contradiction. Thus $N\ge7$.

For completeness, a direct integer audit avoids relying on that equality
description. If all $\pi_i\le1$, the count is nondecreasing in each
$\alpha_i$, and the row bounds give the following four cases up to symmetry:

| $(\pi_1,\pi_2,\pi_3)$ | minimum $(\alpha_1,\alpha_2,\alpha_3)$ | minimum $N$ |
|---|---:|---:|
| $(0,0,0)$ | $(3,3,3)$ | 27 |
| $(0,0,1)$ | $(2,2,3)$ | 15 |
| $(0,1,1)$ | $(1,2,2)$ | 9 |
| $(1,1,1)$ | $(1,1,1)$ | 7 |

This proves the three-row lemma for arbitrary multiplicities and arbitrary
finite $U$.

## 5. Four-row lemma

`PROVED` (four-row lemma): let $\mathcal H$ be a clutter with four members.
If every member has size at least two and every transversal has size at
least three, then

$$
|B(\mathcal H)|\ge6
$$

Form the intersection graph $J$ on the four members. Two vertex-disjoint
edges of $J$ would supply at most two points meeting all four members.
Therefore the matching number of $J$ is at most one.

Suppose first that $J$ has at least two isolated vertices. Blockers factor
over components whose active ground sets are disjoint. Each isolated member
contributes at least two choices. If the other two vertices form a connected
component, its two distinct incomparable members have at least two minimal
transversals: one singleton from their intersection and one pair from their
two differences. Thus this case gives at least $2\times2\times2=8$
blockers. If the remaining vertices are also isolated, it gives at least
$2^4=16$.

Suppose next that $J$ has exactly one isolated member $E$. Let $\mathcal K$
be the connected three-member component. Then

$$
\tau(\mathcal H)=1+\tau(\mathcal K)
$$

so $\tau(\mathcal K)\ge2$. We claim that $|B(\mathcal K)|\ge3$. Put
$\mathcal D=B(\mathcal K)$. If $|\mathcal D|=1$, then
$\mathcal K=B(\mathcal D)$ consists of singletons. If
$|\mathcal D|=2$, the absence of singleton members in
$B(\mathcal D)=\mathcal K$ forces the two members of $\mathcal D$ to be
disjoint. Hence

$$
|\mathcal K|=|D_1||D_2|
$$

But $\tau(\mathcal K)\ge2$ gives $|D_1|,|D_2|\ge2$, contradicting
$|\mathcal K|=3$. Blocker factorization now gives

$$
|B(\mathcal H)|=|E||B(\mathcal K)|\ge2\times3=6
$$

Finally suppose that $J$ has no isolated vertex. A four-vertex graph with no
isolated vertex and matching number at most one must be a three-leaf star.
Let $O$ be the center and $L_1,L_2,L_3$ the leaves. The leaves are pairwise
disjoint, while each meets $O$.

Choose one point from each leaf. The resulting triple is a transversal
exactly when at least one chosen point also lies in $O$. Every such triple is
minimal because no transversal has size at most two. Write
$n_i=|L_i|$. Since $1\le|L_i\cap O|$, the number of these blockers is at
least

$$
n_1n_2n_3-(n_1-1)(n_2-1)(n_3-1)\ge7
$$

The final expression is increasing in each $n_i\ge2$ and equals seven at
$(2,2,2)$. This completes all intersection-graph cases.

## 6. Exact evaluation of the local parameter

`PROVED`: every admissible pair satisfies

$$
|\mathcal S|+|\mathcal C|\ge9
$$

Recall that $a\ge3$ and $b\ge2$.

- If $b=2$, the two-row lemma gives $a\ge9$.
- If $b=3$, the three-row lemma gives $a\ge7$.
- Suppose $b\ge4$. If $a=3$, the three members of $\mathcal S$ are
  pairwise disjoint. Otherwise one point in an intersection and one point
  from the remaining member would form a transversal of size at most two.
  Hence $b=|B(\mathcal S)|\ge2^3=8$.
- If $b\ge4$ and $a=4$, the four-row lemma gives $b\ge6$.
- If $b\ge4$ and $a\ge5$, the sum is already at least nine.

These cases exhaust all admissible integer pairs.

`PROVED`: the bound is attained. Take distinct points
$x_1,x_2,y_1,y_2,w,z$ and define

$$
\mathcal S=
\{\{x_i,y_j\}:i,j\in\{1,2\}\}\cup\{\{w,z\}\}
$$

and

$$
\mathcal C=
\{\{x_1,x_2,w\},\{x_1,x_2,z\},
\{y_1,y_2,w\},\{y_1,y_2,z\}\}
$$

A minimal transversal of $\mathcal C$ that avoids $w,z$ chooses one $x_i$
and one $y_j$. A minimal transversal using $w$ or $z$ must use both, since a
set containing only one of them must still meet both the $x$-pair and the
$y$-pair and is then nonminimal. Therefore

$$
B(\mathcal C)=\mathcal S
$$

Finite blocker involution gives $B(\mathcal S)=\mathcal C$. The five members
of $\mathcal S$ have size two, and the four members of $\mathcal C$ have
size three. Consequently

$$
m(2,3)=9
$$

## 7. Stable global reduction for six layers

Let $s=\operatorname{sat}(6)$ be the eventual stable minimum. By eventual
stability, choose $n$ in the stable range with

$$
n\ge8,\qquad n>2^{30}
$$

Let $X$ be an $n$-element set. Choose an endpoint-normal minimum saturated
6-Sperner family $\mathcal F\subseteq\mathcal P(X)$. The 30-member
construction gives $|\mathcal F|=s\le30$. Hence $n>2^{|\mathcal F|}$, so the
homogeneous-atom theorem supplies an atom $H$ of size at least two. Put
$U=X\setminus H$.

The canonical decomposition has six nonempty saturated-antichain layers:

$$
\mathcal F=\mathcal A_0\mathbin{\dot\cup}\cdots
\mathbin{\dot\cup}\mathcal A_5
$$

Endpoint normalization and the canonical layering give

$$
\mathcal A_0=\{\varnothing\},\qquad \mathcal A_5=\{X\}
$$

Call a member small when it is disjoint from $H$ and large when it contains
$H$. Following canonical predecessors and successors gives, for every
$0\le i\le5$,

$$
|S|\ge i\quad(S\in\mathcal A_i\text{ small}),
\qquad |X\setminus L|\ge5-i\quad(L\in\mathcal A_i\text{ large})
$$

Martin--Veldt Lemma 15 at $k=6$ gives

$$
|\mathcal A_1|\ge5,\qquad |\mathcal A_4|\ge5
$$

## 8. Mutual blockers in the second layer

Let $\mathcal S$ be the small members of $\mathcal A_2$. Write each large
member as $K\cup H$, where $K\subseteq U$, and define

$$
\mathcal C=\{U\setminus K:K\cup H\in\mathcal A_2\}
$$

The size restrictions give

$$
|S|\ge2\quad(S\in\mathcal S),
\qquad |C|\ge3\quad(C\in\mathcal C)
$$

Choose a fixed nonempty proper subset $Q$ of $H$. For every $R\subseteq U$,
the set $R\cup Q$ is not a member of $\mathcal F$. Saturation of the
antichain $\mathcal A_2$ therefore gives

$$
S\subseteq R\text{ for some }S\in\mathcal S,
\qquad\text{or}\qquad
R\subseteq K\text{ for some large trace }K
$$

The antichain property says $S\nsubseteq K$ for every small $S$ and large
trace $K$. Equivalently, every $S$ meets every $C=U\setminus K$.

Every transversal $T$ of $\mathcal C$ is contained in no large trace. The
displayed cover property forces some $S\subseteq T$. Since $\mathcal S$ is
an antichain, the blocker recognition lemma gives

$$
\mathcal S=B(\mathcal C)
$$

Conversely, let $D$ be a transversal of $\mathcal S$ and put $R=U\setminus
D$. No small member lies in $R$, so the cover property gives $R\subseteq K$
for some large trace. Thus $U\setminus K\subseteq D$. The family
$\mathcal C$ is an antichain because complementation reverses containment
among the large traces. Hence

$$
\mathcal C=B(\mathcal S)
$$

The local theorem now gives

$$
|\mathcal A_2|=|\mathcal S|+|\mathcal C|\ge9
$$

For $\mathcal A_3$, the small members have size at least three and the
complements of large traces have size at least two. Exchanging the two sides
of the mutual-blocker pair applies the same theorem and gives

$$
|\mathcal A_3|\ge9
$$

## 9. Final sum

The six layer bounds are

$$
(|\mathcal A_0|,\dots,|\mathcal A_5|)\ge(1,5,9,9,5,1)
$$

Therefore

$$
\operatorname{sat}(6)=|\mathcal F|\ge1+5+9+9+5+1=30
$$

The Morrison--Noel--Scott construction gives the reverse inequality. Hence

$$
\boxed{\operatorname{sat}(6)=30}
$$

## 10. Dependency and boundary audit

- `PROVED`: the local theorem quantifies over arbitrary finite $U$.
- `PROVED`: empty sides are impossible by the member-size conditions and
  finite blocker conventions.
- `PROVED`: repeated point-incidence patterns and nonuniform member sizes are
  allowed.
- `PROVED`: every use of a minimum transversal is finite.
- `PROVED`: the second-layer and third-layer applications are dualized by
  exchanging the two blocker families, not by assuming symmetry of the
  original saturated family.
- `LITERATURE`: eventual stability, endpoint normalization, the homogeneous-
  atom threshold, saturated canonical layers, Lemma 15, and the 30-member
  construction remain cited dependencies.
- `COMPUTED`: finite incidence enumeration is not a proof dependency.
- `UNKNOWN`: novelty, priority, external expert acceptance, and publication
  status.
