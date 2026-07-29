# P0054 G4.5 middle-layer equality exclusion

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_5_COUPLED_LAYER_EQUALITY
OBJECTIVE: EXCLUDE_TOTAL_CANONICAL_SIZE_47
NETWORK: OFFLINE
RESULT: DEPENDENCY_CLOSED_CANDIDATE_PENDING_INDEPENDENT_REVIEW
```

## 1. Scope and conclusion

`PROVED` (relative to the frozen G4--G4.4 canonical-layer inputs): the
middle canonical layer satisfies

\[
|A_3|\ge 10.
\]

`PROVED` (relative to the same frozen inputs): total canonical size (47)
cannot occur.  Indeed, the frozen independent bounds then give

\[
|\mathcal F|
 \ge 1+6+12+10+12+6+1
 =48.
\]

`PROVED` (relative to the frozen eventual-stability reduction): the candidate
global consequence is

\[
\operatorname{sat}(7)\ge48.
\]

`DEFINITION`: the labels above record a dependency-resolved mathematical
candidate.  This file does not modify `claims.yaml` or `status.md`; acceptance
and any claim update belong to a later authorized referee gate.

`UNKNOWN`: the exact value of \(\operatorname{sat}(7)\), novelty, and priority.

The obstruction occurs already inside (A_3).  Consequently no classification
or uniqueness assertion for the twelve-member (A_2,A_4) equality pairs is
needed.

## 2. Frozen middle-layer interface

`DEFINITION`: put (U=X\setminus H).  Let \(\mathcal S\) be the small members
of (A_3).  Write each large member as (K\cup H), and define

\[
\mathcal C=\{U\setminus K:K\cup H\text{ is a large member of }A_3\}.
\]

`PROVED` (frozen canonical predecessor/successor bounds):

\[
|S|\ge3\quad(S\in\mathcal S),
\qquad
|C|\ge3\quad(C\in\mathcal C).
\tag{1}
\]

The first inequality follows along three strict predecessors to (A_0).  The
second follows along three strict successors to (A_6), since

\[
|C|=|U\setminus K|=|X\setminus(K\cup H)|.
\]

`PROVED` (frozen oriented saturation): for every (R\subseteq U),

\[
(\exists S\in\mathcal S)(S\subseteq R)
\quad\text{or}\quad
(\exists C\in\mathcal C)(R\cap C=\varnothing).
\tag{2}
\]

This is the frozen cover with (R\subseteq K) rewritten as
(R\cap(U\setminus K)=\varnothing).

`PROVED` (frozen antichain consequence): \(\mathcal S\) and
\(\mathcal C\) are clutters and

\[
S\cap C\ne\varnothing
\quad\text{for every }S\in\mathcal S, C\in\mathcal C.
\tag{3}
\]

Indeed, (S\cap C=\varnothing) is equivalent to (S\subseteq K), which
would make the small member (S) a strict subset of the large member
(K\cup H) in the same antichain.  Complementing the large traces reverses
containment, so it preserves the clutter property.

## 3. Mutual-blocker recognition

`PROVED`: the middle-layer sides are mutual blockers:

\[
\mathcal S=B(\mathcal C),
\qquad
\mathcal C=B(\mathcal S).
\tag{4}
\]

By (3), every (S\in\mathcal S) is a transversal of \(\mathcal C\).  If
(T\) is any transversal of \(\mathcal C\), apply (2) with (R=T).  The
second alternative is impossible: if (T\cap C=\varnothing) for some
(C\in\mathcal C), then (T) does not meet that member of \(\mathcal C\).
Thus some (S\in\mathcal S) satisfies (S\subseteq T).  Since
\(\mathcal S\) is an antichain, these two facts identify it with all
inclusion-minimal transversals of \(\mathcal C\).

Conversely, (3) makes every (C\in\mathcal C) a transversal of
\(\mathcal S\).  If (T) is any transversal of \(\mathcal S\), apply (2)
to (R=U\setminus T).  No (S\in\mathcal S) can be contained in (R), so
there is a (C\in\mathcal C) with (R\cap C=\varnothing), equivalently
(C\subseteq T).  The antichain property of \(\mathcal C\) gives the second
blocker equality.

`PROVED`: both sides in (4) are nonempty.  At (R=U), (1) prevents the
second alternative in (2), so \(\mathcal S\ne\varnothing\).  At
(R=\varnothing), (1) prevents the first alternative, so
\(\mathcal C\ne\varnothing\).

`PROVED` (private-witness bound): if (T\in B(\mathcal H)), then

\[
|T|\le |\mathcal H|.
\tag{5}
\]

For every (x\in T), minimality supplies an (E_x\in\mathcal H) with
(E_x\cap T=\{x\}).  Distinct points require distinct private witnesses,
which proves (5).

Put

\[
a=|\mathcal S|,\qquad b=|\mathcal C|.
\]

`PROVED`: (1), (4), and (5) imply

\[
a\ge3,\qquad b\ge3.
\tag{6}
\]

## 4. Two small-clutter blocker lemmas

`LITERATURE` (frozen G4.4 blocker input): every finite clutter satisfies

\[
B(B(\mathcal H))=\mathcal H.
\tag{7}
\]

`PROVED` (disjoint-component factorization): if two nonempty families use
disjoint active ground sets, a minimal transversal of their union is exactly
the union of one minimal transversal from each family.  Meeting and
minimality both restrict componentwise.  Hence blocker cardinalities
multiply.  In particular,

\[
|B(\{E\})|=|E|
\tag{8}
\]

for every nonempty set (E).

`PROVED` (non-uniqueness lemma): if a nonempty clutter \(\mathcal K\) has
all members of size at least three and transversal number at least two, then

\[
|B(\mathcal K)|\ge2.
\tag{9}
\]

The blocker is nonempty by finiteness.  If (B(\mathcal K)=\{T\}), then
(7) gives

\[
\mathcal K=B(\{T\})=\{\{t\}:t\in T\},
\]

contradicting the member-size lower bound.  The transversal-number assumption
also excludes (T=\varnothing).

`PROVED` (three-member lemma): let

\[
\mathcal H=\{E_1,E_2,E_3\},
\qquad |E_i|\ge3,
\qquad \tau(\mathcal H)\ge3.
\]

Then

\[
|B(\mathcal H)|\ge27.
\tag{10}
\]

If (x\in E_i\cap E_j), then (x), together with any point of the remaining
member, is a transversal of size at most two.  Thus the three members are
pairwise disjoint.  Choosing one point from each member gives

\[
|E_1||E_2||E_3|\ge3^3=27
\]

distinct minimal transversals, proving (10).

`PROVED` (four-member lemma): let

\[
\mathcal H=\{E_1,E_2,E_3,E_4\},
\qquad |E_i|\ge3,
\qquad \tau(\mathcal H)\ge3.
\]

Then

\[
|B(\mathcal H)|\ge6.
\tag{11}
\]

Form the intersection graph (G) on the four members.  Two vertex-disjoint
graph edges would supply two points meeting all four members, contradicting
\(\tau(\mathcal H)\ge3\).  Hence the matching number of (G) is at most one.

If (G) has at least two isolated vertices, factor off their corresponding
sets using (8).  Any remaining finite family has a minimal transversal, so

\[
|B(\mathcal H)|\ge3^2=9.
\]

If (G) has exactly one isolated vertex with corresponding set (E), let
\(\mathcal K\) be the other three members.  A singleton transversal of
\(\mathcal K\), together with one point of (E), would be a two-point
transversal of \(\mathcal H\).  Thus \(\tau(\mathcal K)\ge2\), and (8)--(9)
give

\[
|B(\mathcal H)|=|B(\mathcal K)|\,|E|\ge2\cdot3=6.
\]

It remains that (G) has no isolated vertex.  A graph of matching number at
most one is either a star, or all its edges lie in a triangle: after choosing
two adjacent edges (uv,uw), an edge avoiding (u) must be (vw), since
otherwise it is disjoint from one of the chosen edges.  The triangle option
would leave the fourth vertex isolated.  Therefore (G=K_{1,3}).

Let (E_0) be the center and (L_1,L_2,L_3) the pairwise-disjoint leaves.
Put

\[
p_i=|L_i\setminus E_0|,
\quad q_i=|L_i\cap E_0|,
\quad
c=\left|E_0\setminus\bigcup_iL_i\right|.
\]

Here (p_i+q_i=|L_i|\ge3) and (q_i\ge1).  A minimal transversal either
chooses one point from each leaf with at least one chosen point in (E_0), or
chooses one point from each (L_i\setminus E_0) and one center-exclusive
point.  These cases are disjoint and exhaustive, so

\[
|B(\mathcal H)|
=\prod_i(p_i+q_i)-\prod_i p_i+c\prod_i p_i.
\tag{12}
\]

If (c\ge1), (12) is at least
\(\prod_i(p_i+q_i)\ge27\).  If (c=0), fix any (i); expanding first in
that coordinate gives

\[
\prod_j(p_j+q_j)-\prod_jp_j
\ge q_i\prod_{j\ne i}(p_j+q_j)
\ge1\cdot3\cdot3=9.
\]

This completes every graph case and proves (11).

## 5. Exclusion of a nine-member middle layer

Assume (a+b=9).

`PROVED`: by (6), the only ordered splits are

\[
(a,b)=(6,3),(5,4),(4,5),(3,6).
\tag{13}
\]

`PROVED`: the split ((6,3)) is impossible.  Apply (10) to
\(\mathcal C\): its three members have size at least three, and
\(\tau(\mathcal C)\ge3\) because
\(B(\mathcal C)=\mathcal S\) has no member smaller than three.  It follows
that (a=|B(\mathcal C)|\ge27), contrary to (a=6).

`PROVED`: the split ((5,4)) is impossible.  Apply (11) to
\(\mathcal C\) to obtain (a=|B(\mathcal C)|\ge6), contrary to (a=5).

`PROVED`: the split ((4,5)) is impossible.  Apply (11) to the four-member
family \(\mathcal S\) to obtain (b=|B(\mathcal S)|\ge6), contrary to
(b=5).

`PROVED`: the split ((3,6)) is impossible.  Apply (10) to the three-member
family \(\mathcal S\) to obtain (b=|B(\mathcal S)|\ge27), contrary to
(b=6).

`PROVED`: (13) is exhausted, so (a+b\ne9).  The frozen lower bound
\(|A_3|\ge9\) therefore strengthens to

\[
|A_3|\ge10.
\]

## 6. Failed route and exact counterexample

`REFUTED`: the first attempted extension asserted that the intersection graph
of a five-member clutter with transversal number at least three must also have
matching number at most one.  This is false.  On pairwise distinct points,
take

\[
\begin{aligned}
E_1&=\{a,x_1,x_2\},& E_2&=\{a,y_1,y_2\},\\
E_3&=\{b,z_1,z_2\},& E_4&=\{b,w_1,w_2\},\\
E_5&=\{c_1,c_2,c_3\}.&&
\end{aligned}
\]

Its intersection graph has the two-edge matching
\(E_1E_2,E_3E_4\).  The set \(\{a,b,c_1\}\) is a three-point transversal.
Every transversal needs a point of (E_5), a point meeting the first pair,
and a point meeting the second pair; the three active ground parts are
disjoint.  Hence the transversal number is exactly three.  The invalid step
was treating the resulting three-point transversal as a contradiction.

`PROVED`: the completed argument does not use any five-member intersection-
graph assertion.  In the ((4,5)) split it applies the four-member lemma to
the opposite blocker side.

## 7. Boundary and dependency audit

- `PROVED`: (U) is arbitrary and finite; no bound on \(|U|\) is used.
- `PROVED`: repeated point-incidence patterns and empty incidence classes are
  allowed; the proof works with actual points and set intersections.
- `PROVED`: member sizes may be nonuniform and may exceed three.
- `PROVED`: both blocker sides, empty/full core tests, and minimum-transversal
  existence are handled explicitly.
- `PROVED`: no computation, probability estimate, compactness argument,
  complement symmetry of the global family, or equality-case uniqueness for
  (m(2,4)=12) is used.
- `PROVED`: the only non-elementary frozen input inside the new local argument
  is finite blocker involution (7).

| Dependency node | Label | Depends on |
|---|---|---|
| middle size bounds and oriented cover | `PROVED` | frozen G4 canonical predecessor/successor and saturation interface |
| mutual-blocker recognition | `PROVED` | oriented cover and layer antichain |
| three-member lemma | `PROVED` | elementary intersection and product count |
| four-member lemma | `PROVED` | intersection graph, disjoint factorization, finite blocker involution |
| exclusion of \(|A_3|=9\) | `PROVED` | mutual blockers and the two small-clutter lemmas |
| exclusion of total 47 | `PROVED` | \(|A_3|\ge10\) and frozen layer minima |
| candidate \(\operatorname{sat}(7)\ge48\) | `PROVED` | exclusion of total 47 and frozen eventual-stability reduction |

```text
FIRST_INVALID_STEP: FIVE_EDGE_INTERSECTION_GRAPH_MATCHING_NUMBER_AT_MOST_ONE
UNRESOLVED_MATHEMATICAL_DEPENDENCIES: NONE_WITHIN_FROZEN_INPUTS
FINITE_SEARCH_USED_AS_PROOF: NO
CLAIMS_OR_STATUS_MODIFIED: NO
```
