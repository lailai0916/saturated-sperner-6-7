# P0054 G4.13 scratch: three pair blockers are forced

```text
STATUS: PROVED_CANDIDATE
SCOPE: FIVE_ROW_KERNEL_IN_THE_G4.12_(8,8)_BRANCH
RESULT: BLOCKERS_AT_MOST_8_IMPLIES_EXACTLY_3_PAIR_BLOCKERS
NETWORK: MATHEMATICS_OFFLINE
```

## Statement

Let $\mathcal K$ be a finite five-row clutter. Assume:

- every row has size at least three;
- every active point has $\mathcal K$-degree at most three;
- $B(\mathcal K)$ has at most three two-point rows.

Then:

$$
|B(\mathcal K)|\le8
\implies
|\{T\in B(\mathcal K):|T|=2\}|=3
$$

Equivalently, if $B(\mathcal K)$ has at most two two-point rows, then
$|B(\mathcal K)|\ge9$.

This statement allows arbitrary finite ground sets, parallel actual points,
repeated incidence supports, nonuniform row sizes, and inactive points.

## Degree reduction

Assume for contradiction that

$$
\begin{aligned}
  |B(\mathcal K)| & \le8 \\
  |\{T\in B(\mathcal K):|T|=2\}| & \le2
\end{aligned}
\tag{1}
$$

If every point has degree at most two, represent the active points as actual
loops and nonloop edges on the five row indices. Choose an
inclusion-minimal sub-multigraph whose five row degrees remain at least three.
The pure loop-multigraph lemma in
`/tmp/p0054_g413_loop_multigraph_lemma.md` gives at least nine minimal actual
edge covers. Each is a blocker of $\mathcal K$, contradicting (1). This
argument preserves loops and parallel actual points and has no finite-search
dependency.

Fix a point $x$ of degree three. Write the rows containing $x$ as

$$
A_i=\{x\}\cup L_i\text{ for }i\in\{1,2,3\}
$$

and let $P,Q$ be the two rows avoiding $x$. Put

$$
\begin{aligned}
  c & =|P\cap Q| \\
  a & =|P\setminus Q| \\
  b & =|Q\setminus P|
\end{aligned}
\tag{2}
$$

The clutter property gives $a,b\ge1$. Every $y\in P\cap Q$ gives the pair
blocker $\{x,y\}$. The point $x$ is necessary because $y$ has degree at most
three and already lies in $P,Q$. Hence (1) gives $c\le2$.

The minimal transversals of $\{P,Q\}$ are:

- the $c$ singleton sets from $P\cap Q$;
- the $ab$ cross-pairs from $(P\setminus Q)\times(Q\setminus P)$.

Thus their number is

$$
N=c+ab
\tag{3}
$$

For each such transversal $S$, use $S$ if it hits $A_1,A_2,A_3$, and use
$S\cup\{x\}$ otherwise. Private rows $P,Q$, together with a missed $A_i$ in
the second case, prove that this is an injection into $B(\mathcal K)$.

Let $h$ be the number of injection images avoiding $x$. A singleton from
$P\cap Q$ cannot hit all three $A_i$, so these $h$ images are pair blockers.
Together with the $c$ pair blockers $\{x,y\}$, (1) gives

$$
h+c\le2
\tag{4}
$$

Delete $x$ and minimize:

$$
\begin{aligned}
  \mathcal R & =\min\{P,Q,L_1,L_2,L_3\} \\
  \mathcal T & =B(\mathcal R)
\end{aligned}
\tag{5}
$$

The residual-blocker lemma identifies $\mathcal T$ with the blockers of
$\mathcal K$ avoiding $x$. The $h$ injection images avoiding $x$ already lie
in $\mathcal T$, while the other $N-h$ images contain $x$. Therefore

$$
|B(\mathcal K)|\ge N-h+|\mathcal T|
\tag{6}
$$

The following properties of the residual pair will be used repeatedly:

1. $|\mathcal R|\le5$ and every row of $\mathcal R$ has size at least two.
2. At most three rows of $\mathcal R$ have size two, because only the three
   sets $L_i$ can have size two.
3. Every point has $\mathcal R$-degree at most three.
4. Every row of $\mathcal T$ has size at most $|\mathcal R|\le5$ by private
   rows.
5. At most $2-c$ rows of $\mathcal T$ have size two.

All later finite reductions retain these five properties.

## Disjoint avoiding rows

If $c=0$, then $|P|,|Q|\ge3$, so (3) gives $N\ge9$. The injection alone
contradicts (1). Hence $c\in\{1,2\}$.

## One common point

Suppose $c=1$. Then $a,b\ge2$, so $N\ge5$, while (4) gives $h\le1$.
It is enough by (6) to prove

$$
|\mathcal T|\ge5
\tag{7}
$$

One or two rows in $\mathcal T$ are impossible. In the two-row case, the rows
must be disjoint because $B(\mathcal T)=\mathcal R$ has no singleton row.
One row of $\mathcal T$ may be a pair and the other has size at least three,
so their blocker has at least six rows, contradicting $|\mathcal R|\le5$.

For three rows, the pure three-row lemma in
`/tmp/p0054_g413_small_residual_lemmas.md` gives
$|\mathcal R|\ge5$. Equality forces all five rows of $\mathcal R$ to be
pairs, contradicting its three-pair limit.

It remains to exclude $|\mathcal T|=4$. Every row of $\mathcal T$ has size
from two through five, at most one is a pair, and $B(\mathcal T)=\mathcal R$
has at most five rows of size at least two. Lemma 1 in
`/private/tmp/p0054_g413_residual_lemmas_v3.md` shows that $\mathcal R$ has exactly
three pair rows and two triple rows, and that the triples intersect in two
points. In particular $|\mathcal R|=5$, so all five inputs in (5) are
retained. The two triples are therefore $P,Q$, but $|P\cap Q|=c=1$. This is a
contradiction.

This proves (7). Equations (3), (4), and (6) now give

$$
|B(\mathcal K)|\ge5-1+5=9
$$

## Two common points

Suppose $c=2$. Equations (3) and (4) give

$$
\begin{aligned}
  N & \ge3 \\
  h & =0
\end{aligned}
\tag{8}
$$

All rows of $\mathcal T$ therefore have size at least three. It is enough to
prove

$$
|\mathcal T|\ge6
\tag{9}
$$

Private rows give $|\mathcal R|\ge3$, while (5) gives
$|\mathcal R|\le5$. Every row of $\mathcal R$ has size at least two, at most
three are pairs, and every row of $B(\mathcal R)=\mathcal T$ has size at least
three. Lemma 2 in `/private/tmp/p0054_g413_residual_lemmas_v3.md` applies directly and
gives $|\mathcal T|\ge6$.

This proves (9). Finally, (6) and (8) give

$$
|B(\mathcal K)|\ge3+6=9
$$

The cases $c=0,1,2$ are exhaustive. This contradicts (1) and proves the
statement.

## Replacing the five-row active-mask scan

The G4.12 five-row kernel already has at most eight blockers and at most three
pair blockers. The proved-candidate statement above therefore forces exactly
three pair blockers before any five-row classification begins.

The exact-pair generator works directly with the 25 support multiplicities.
It orders supports by decreasing rank and precomputes the 396 minimal support
covers. Whenever the last support of a cover receives its multiplicity, the
new actual blockers are added immediately. These counts are monotone, so a
branch stops as soon as it has more than eight blockers or more than three
pair blockers. Once the singleton supports begin, the pair count can no
longer change and must already equal three.

The generator visits 19188518 recursion states and reaches 2435 complete
row-bounded vectors. After the clutter and double-blocker-use checks, it
retains exactly:

```text
multiplicity_vectors=1890
blockers_6_pairs_3=20
blockers_7_pairs_3=470
blockers_8_pairs_3=1400
row_permutation_classes=24
```

All 24 canonical keys agree byte-for-byte with the original active-mask
output. Thus the classification is still `COMPUTED`, but the primary route no
longer enumerates $2^{25}-1$ active support masks.

## Evidence boundary

The residual lower bound is now `PROVED_CANDIDATE`; it no longer depends on a
finite table. The degree-at-most-two support-multigraph branch is also
`PROVED_CANDIDATE`. The later 24-class generator remains `COMPUTED`. Its
reduction is arbitrary-finite:

- private rows bound every enumerated row size by five;
- a point common to all residual rows would create a singleton blocker, so
  only proper nonempty supports occur;
- the inherited degree-three bound leaves exactly 25 supports in the
  five-row residual case;
- multiplicities preserve parallel actual points;
- row-size profiles include nonuniform rows and empty incidence classes;
- inactive points occur in no minimal transversal and need not be enumerated.

The pair-blocker lemma and exact-pair generator together remove the
33554431-mask scan from the primary five-row classification. The resulting 24
classes remain `COMPUTED`; the later degree obstruction still consumes those
classes after their three pair blockers acquire the external point.

```text
PROFILE_GENERATOR: /tmp/p0054_g413_profile_generator.cpp
PROFILE_RESULT: /tmp/p0054_g413_profile_generator_results.txt
SMALL_CERTIFICATE: /tmp/p0054_g413_residual_small_certificate.py
MASK_CROSSCHECK: /tmp/p0054_g413_residual_five_row_results.txt
LOOP_MULTIGRAPH_PROOF: /tmp/p0054_g413_loop_multigraph_lemma.md
SMALL_RESIDUAL_PROOF: /tmp/p0054_g413_small_residual_lemmas.md
PURE_RESIDUAL_PROOF: /private/tmp/p0054_g413_residual_lemmas_v3.md
EXACT_PAIR_GENERATOR: /tmp/p0054_g413_exact_pair_generator.cpp
EXACT_PAIR_RESULT: /tmp/p0054_g413_exact_pair_generator_results.txt
```
