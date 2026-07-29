# P0054 G4.2 Prover B: abstract hypergraph transversal

```text
ROLE: ISOLATED_COMPATIBILITY_PROVER_B
SUBPROBLEM: FOUR_SMALL_THREE_LARGE_COMPLEMENTS
VERDICT: PROVED
FIRST_UNCERTAIN_STEP_FOR_THIS_SUBPROBLEM: NONE
NETWORK: NOT_USED
FORMALIZER: NOT_USED
OTHER_G4_2_AGENT_OUTPUTS: NOT_READ
```

## 1. Exact theorem

`PROVED` (**four-small/three-complement theorem**). Let $U$ be a finite
set. Let $S_1,S_2,S_3,S_4\subseteq U$ and
$C_1,C_2,C_3\subseteq U$ satisfy

\[
|S_i|\ge 2,\qquad |C_j|\ge 4,\qquad
S_i\cap C_j\ne\varnothing\quad(1\le i\le4,\ 1\le j\le3).
\]

The same-side antichain hypotheses from the frozen subproblem may also be
imposed, but are not needed. There is a set $R\subseteq U$ such that

\[
R\cap C_j\ne\varnothing\quad(j=1,2,3),
\qquad
S_i\nsubseteq R\quad(i=1,2,3,4).
\]

Thus the frozen statement is true for arbitrary finite $U$, arbitrary
nonuniform sizes above the displayed lower bounds, and arbitrary
multiplicities of incidence patterns.

`PROVED`. The set $R$ may be chosen inclusion-minimal among the
transversals with the required avoidance property, and then $|R|\le3$.
Indeed, choosing one element of $R\cap C_j$ for each of the three labels
produces a transversal contained in $R$; minimality makes that selected set
equal to $R$. This is exactly the allowed-merge interpretation of choosing
one hit from each $C_j$.

## 2. Reduction to the blocker of three sets

`DEFINITION`. A **transversal** of
$\mathcal C=\{C_1,C_2,C_3\}$ is a set meeting every $C_j$.
Its **blocker** $b(\mathcal C)$ is the family of inclusion-minimal
transversals. The three $C_j$ are treated as labelled here; the definition
still works if two labelled sets happen to be equal.

`PROVED`. Suppose, for contradiction, that the required $R$ does not
exist. Every transversal $T$ of $\mathcal C$ then contains at least one
$S_i$. On the other hand, every $S_i$ is itself a transversal, because
it meets each $C_j$. If $T\in b(\mathcal C)$ and $S_i\subseteq T$, the
minimality of $T$, together with the fact that $S_i$ is a transversal,
forces $T=S_i$. Consequently

\[
b(\mathcal C)\subseteq\{S_1,S_2,S_3,S_4\},
\qquad |b(\mathcal C)|\le4,                              \tag{1}
\]

and every member of $b(\mathcal C)$ has size at least two.

`PROVED`. It follows that

\[
C_1\cap C_2\cap C_3=\varnothing.                         \tag{2}
\]

Indeed, an element in the triple intersection would by itself be an
inclusion-minimal transversal, contradicting the last conclusion of the
previous paragraph.

## 3. Exact incidence-pattern classification

`DEFINITION`. By (2), every element of
$C_1\cup C_2\cup C_3$ has one of six nonempty incidence patterns. For
$\{i,j,k\}=\{1,2,3\}$, let

\[
A_i=C_i\setminus(C_j\cup C_k),\qquad
P_i=(C_j\cap C_k)\setminus C_i,
\]

and write $a_i=|A_i|$, $p_i=|P_i|$. Thus $P_i$ is the pair-incidence
class missing $C_i$. Elements outside $C_1\cup C_2\cup C_3$ cannot occur
in an inclusion-minimal transversal and are irrelevant. We have

\[
|C_i|=a_i+p_j+p_k\ge4.                                  \tag{3}
\]

`PROVED`. Every member of $b(\mathcal C)$ has size at most three. Given a
minimal transversal $T$, choose $x_i\in T\cap C_i$ for each $i$. The
set $\{x_1,x_2,x_3\}\subseteq T$ is a transversal, so minimality makes it
equal to $T$.

`PROVED`. The two-element members of $b(\mathcal C)$ are exactly

* one element from $A_i$ and one from $P_i$, for some $i$; or
* one element from each of $P_i,P_j$, for some $i\ne j$.

In either case the two incidence supports cover all three labels and neither
element alone does. No other pair of the six patterns covers all three
labels.

`PROVED`. The three-element members of $b(\mathcal C)$ are exactly the
sets having one element in each of $A_1,A_2,A_3$. To prove the forward
direction, let $T$ be a minimal three-element transversal. For each
$x\in T$, minimality supplies a label $i(x)$ for which
$T\cap C_{i(x)}=\{x\}$. The three witness labels are distinct. They
therefore use all three labels. If $x$ also belonged to the witness set of
another member of $T$, that other member would not be its unique
intersection; hence $x$ belongs only to its own witness set. The converse
follows because deleting the $A_i$-element leaves $C_i$ unhit.

`PROVED`. The classification is disjoint and gives the exact blocker count

\[
B:=|b(\mathcal C)|
 =a_1a_2a_3+\sum_{i=1}^3a_ip_i
  +p_1p_2+p_1p_3+p_2p_3.                                \tag{4}
\]

This formula includes zero incidence classes and arbitrary repeated
incidence patterns.

## 4. Lower bound $B\ge12$

`PROVED`. If some $p_i\ge3$, then the terms in (4) that contain $p_i$
include

\[
p_i(a_i+p_j+p_k)=p_i|C_i|\ge3\cdot4=12,
\]

and all omitted terms in (4) are nonnegative. Hence $B\ge12$.

`PROVED`. It remains to consider $0\le p_i\le2$ for all $i$. Equation
(3) gives

\[
a_i\ge a_i^{(0)}:=4-p_j-p_k\ge0.                         \tag{5}
\]

The right side of (4) is nondecreasing in every $a_i$: increasing $a_i$
by one changes it by $a_ja_k+p_i\ge0$. It is therefore enough to substitute
$a_i=a_i^{(0)}$. Formula (4) and the constraints are invariant under
permuting the three labels, so order $p_1\le p_2\le p_3$. The following
table contains all ten multisets from $\{0,1,2\}$; every entry is the direct integer
value of (4).

| $(p_1,p_2,p_3)$ | $(a_1^{(0)},a_2^{(0)},a_3^{(0)})$ | $B_0$ |
|---|---:|---:|
| $(0,0,0)$ | $(4,4,4)$ | 64 |
| $(0,0,1)$ | $(3,3,4)$ | 40 |
| $(0,0,2)$ | $(2,2,4)$ | 24 |
| $(0,1,1)$ | $(2,3,3)$ | 25 |
| $(0,1,2)$ | $(1,2,3)$ | 16 |
| $(0,2,2)$ | $(0,2,2)$ | 12 |
| $(1,1,1)$ | $(2,2,2)$ | 17 |
| $(1,1,2)$ | $(1,1,2)$ | 13 |
| $(1,2,2)$ | $(0,1,1)$ | 12 |
| $(2,2,2)$ | $(0,0,0)$ | 12 |

Thus $B\ge B_0\ge12$ in the remaining case as well.

`PROVED`. This contradicts (1). The contradiction proves the theorem.
The ten-row arithmetic check is a classification of the three unbounded
incidence multiplicities after the $p_i\ge3$ case has already been removed;
it is not an enumeration of $U$, of $|U|$, or of set systems up to a
chosen bound.

## 5. Assumption and boundary audit

`PROVED`.

* **Arbitrary large $U$:** only the six incidence-class cardinalities enter
  (4). Any number of elements outside all $C_j$ is ignored for the proved
  minimality reason above.
* **Nonuniform and strict inequalities:** (3) is imposed separately for each
  $C_i$. If a size exceeds four, either the $p_i\ge3$ argument applies or
  the corresponding $a_i$ exceeds (5), and monotonicity preserves the
  lower bound. The $S_i$ have no upper-size restriction.
* **Empty or repeated incidence classes:** zeros occur explicitly in the
  table, while arbitrary positive multiplicities are represented by the six
  integers in (4).
* **Duplicate-set boundary:** neither same-side incomparability nor
  distinctness is used. Repeated $S_i$ only decreases the right side of
  (1); repeated labelled $C_j$ is still covered by the six-pattern
  classification. The frozen antichain hypotheses are therefore redundant
  for this subproblem.
* **Used hypotheses:** finiteness supplies inclusion-minimal transversals;
  every cross-intersection makes each $S_i$ a transversal; $|S_i|\ge2$
  excludes singleton blocker members under the contradiction assumption;
  the three bounds $|C_i|\ge4$ drive (3). No Hall assumption, uniformity,
  probability estimate, or bounded-ground-set reduction is used.

`PROVED` (stronger cardinality form). The same argument proves the conclusion
with any family of at most eleven small sets satisfying the same
cross-intersection and size-at-least-two conditions: a hypothetical failure
would give $b(\mathcal C)$ as a subfamily of those small sets, whereas
$|b(\mathcal C)|\ge12$.

`PROVED` (sharpness of the number 12 for the blocker bound). Let
$U=P_1\mathbin{\dot\cup}P_2\mathbin{\dot\cup}P_3$, with $|P_i|=2$, and set

\[
C_1=P_2\cup P_3,\qquad C_2=P_1\cup P_3,\qquad
C_3=P_1\cup P_2.
\]

Then the three $C_i$ are pairwise incomparable four-sets and their blocker
is exactly the twelve pairs having endpoints in two different $P_i$.
Taking those twelve pairs as the small family makes the requested $R$
impossible. Thus the lower bound 12 in this proof cannot be raised.

`PROVED` (the given four-set lower bound is stronger than necessary). If
only $|C_i|\ge3$ is assumed, the same proof gives
$|b(\mathcal C)|\ge6>4$. Indeed, if some $p_i\ge2$, then
$B\ge p_i|C_i|\ge6$. Otherwise $p_i\in\{0,1\}$; after sorting,
the four possible triples `000,001,011,111`, with
$a_i=3-p_j-p_k$, give respectively $B_0=27,15,9,7$.

`REFUTED` (further weakening all complement sizes to two). On
$U=\{x,y,z,w\}$, let

\[
C_1=\{y,z\},\qquad C_2=\{x,z\},\qquad C_3=\{x,y,w\},
\]

and let the four small sets be

\[
\{w,z\},\quad\{x,y\},\quad\{x,z\},\quad\{y,z\}.
\]

The two same-side families are antichains, every small set meets every
$C_j$, and the displayed four pairs are exactly $b(\mathcal C)$. Hence
every transversal contains a complete small set. This is a direct finite
check showing that the sufficient uniform lower bound three cannot be
replaced by two.

## 6. Relation to frozen C17 material and remaining uncertainty

`PROVED` (dependency direction). The abstract proof uses from the frozen G4
candidate only the set-theoretic interface relevant to a second internal
layer: small generators have size at least two, large-trace complements have
size at least four, every small generator meets every large complement, and
oriented saturation would forbid the desired $R$. It does not use the
numerical conclusion $\operatorname{sat}(7)\ge37$, any G0--G3 certificate,
or any unlisted G4.2 output. There is therefore no circular dependency on the
frozen C17 result.

`PROVED` (application scope). If a hypothetical seven-member $A_2$ has
exactly four small members and three large members, oriented saturation says
that no such $R$ exists, while the theorem above constructs one. Hence that
specific $4+3$ split is impossible.

`UNKNOWN` (outside this isolated task). This report does not classify the
other small/large splits of a seven-member $A_2$. Therefore it does not by
itself establish $|A_2|\ge8$, strengthen the global C17 conclusion, or
authorize any status/claims change. For the exact abstract $4+3$ theorem,
there is no uncertain proof step; for the full G4.2 target, the first
remaining step is the separately assigned exclusion or realization of the
other splits.
