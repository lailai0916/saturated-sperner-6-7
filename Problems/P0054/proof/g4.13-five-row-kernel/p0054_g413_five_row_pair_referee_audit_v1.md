# P0054 G4.13 five-row pair lemma Referee audit v1

```text
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
REVIEWED_ARTIFACT: p0054_g413_five_row_pair_lemma_v5.md
STATUS: PROVED_CANDIDATE
DEPENDENCY_BOUNDARY: CONDITIONAL_ON_ACCEPTED_G4.9_AND_RESIDUAL_LEMMAS
NETWORK: MATHEMATICS_OFFLINE
FORMAL_PROMOTION: NO
```

## Statement audit

Let $\mathcal K$ be a finite five-row clutter. Assume every row has size at
least three, every active point has degree at most three, and $B(\mathcal K)$
has at most three pair rows. The reviewed implication is:

$$
|B(\mathcal K)|\le8
\implies
|\{T\in B(\mathcal K):|T|=2\}|=3
$$

The proof argues contrapositively. If the pair count is at most two, then
$|B(\mathcal K)|\ge9$.

The statement allows arbitrary finite ground sets, parallel actual points,
repeated supports, nonuniform row sizes, and inactive points.

## Degree-at-most-two branch

If every active point has degree at most two, represent each actual point by
a loop or nonloop edge on the five row indices. Choose an inclusion-minimal
submultigraph whose five vertex degrees remain at least three.

Every minimal actual edge cover of this submultigraph is a blocker of
$\mathcal K$. Coverage is unchanged at the row level. Minimality supplies a
private row for every selected actual point.

The loop-multigraph lemma gives at least nine minimal actual edge covers. Its
case split by the number of degree-three vertices is exhaustive:

- three low vertices give at least nineteen selector covers;
- four low vertices give at least ten covers;
- five low vertices give at least nine covers, including all loop cases.

Loops count once in the row degree. Parallel copies remain distinct actual
points. No support simplification loses multiplicity.

## Degree-three residual split

Fix a point $x$ of degree three. Write its rows as
$A_i=\{x\}\cup L_i$ and the two avoiding rows as $P,Q$. Put:

$$
c=|P\cap Q|,
\qquad
a=|P\setminus Q|,
\qquad
b=|Q\setminus P|
$$

Every $y\in P\cap Q$ gives the pair blocker $\{x,y\}$. The point $x$ has a
private row because $y$ can occur in at most one of the three $A_i$. Hence
$c\le2$ under the assumed two-pair budget.

The minimal transversals of $\{P,Q\}$ consist of $c$ singletons and $ab$
cross-pairs. Each maps injectively to a blocker of $\mathcal K$: retain it if
it hits all three $A_i$, and otherwise adjoin $x$. Private rows in $P,Q$ and
a missed $A_i$ prove minimality.

Let $h$ be the number of images avoiding $x$. These are pair blockers, while
the $c$ blockers $\{x,y\}$ contain $x$. Therefore $h+c\le2$.

Delete $x$ and minimize:

$$
\mathcal R=\min\{P,Q,L_1,L_2,L_3\},
\qquad
\mathcal T=B(\mathcal R)
$$

The residual-blocker identity gives exactly the blockers of $\mathcal K$
that avoid $x$. It is valid after minimization because a minimal transversal
depends only on the inclusion-minimal source rows.

The inherited properties are complete:

- $|\mathcal R|\le5$ and every row has size at least two;
- at most three rows of $\mathcal R$ are pairs;
- every point has $\mathcal R$-degree at most three;
- every row of $\mathcal T$ has size at most five by private rows;
- at most $2-c$ rows of $\mathcal T$ are pairs.

The injection and residual families are disjoint except for the $h$ images
already counted inside $\mathcal T$. Thus:

$$
|B(\mathcal K)|\ge c+ab-h+|\mathcal T|
$$

## The three values of c

For $c=0$, the rows $P,Q$ are disjoint and have size at least three. Hence
$ab\ge9$, so the injection alone gives nine blockers.

For $c=1$, one has $a,b\ge2$ and $h\le1$. It remains to prove
$|\mathcal T|\ge5$.

- One or two rows in $\mathcal T$ reconstruct singleton rows or at least six
  residual rows.
- Three rows are excluded by the pure three-row lemma. Equality at five
  would make all five rows of $\mathcal R$ pairs.
- Four rows are excluded by residual Lemma 1. It forces the two large rows of
  $\mathcal R$ to be triples meeting in two points. They must be $P,Q$, which
  meet in one point.

Therefore $|B(\mathcal K)|\ge5-1+5=9$.

For $c=2$, the pair budget forces $h=0$. Every row of $\mathcal T$ has size
at least three. Private rows give $3\le|\mathcal R|\le5$, and
$\tau(\mathcal R)\ge3$. Residual Lemma 2 gives $|\mathcal T|\ge6$. Hence:

$$
|B(\mathcal K)|\ge3+6=9
$$

The values $c=0,1,2$ are exhaustive.

## Dependency audit

The proof has no dependence on the old active-mask scan or the 24 canonical
classes. Its primary dependencies are:

- the pure loop-multigraph lemma;
- the pure three-row and four-large-row residual lemmas;
- residual Lemmas 1 and 2 in `p0054_g413_residual_lemmas_v3.md`;
- the accepted G4.9 four-row and five-row lower bounds used inside those
  residual lemmas.

The exact-pair generator, 1,890 multiplicity vectors, and 24 row-permutation
classes remain `COMPUTED` cross-checks. They are not dependencies of the
three-pair conclusion.

## Verdict

`FIRST_INVALID_STEP: NONE`.

The reviewed five-row statement reaches `PROVED_CANDIDATE`. This audit does
not promote G4.12, G4.13, or $\operatorname{sat}(7)=55$ to the formal claim
ledger. It does not establish novelty or Lean formalization.

