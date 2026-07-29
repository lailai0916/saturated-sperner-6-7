# P0054 G4.5 candidate: the 47-member equality is impossible

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_5_COUPLED_LAYER_EQUALITY
TARGET: exclude (|A_0|,...,|A_6|)=(1,6,12,9,12,6,1)
CANDIDATE_CONCLUSION: sat(7) >= 48
STATUS: PROVED_CANDIDATE_PENDING_REFEREE_RECONSTRUCTION
NETWORK: OFFLINE
```

## 1. Statement and dependency boundary

`PROVED` (relative to the frozen G4.5 input): in the canonical decomposition
of a minimum saturated 7-Sperner family, the equality profile

```text
(|A_0|,...,|A_6|)=(1,6,12,9,12,6,1)
```

cannot occur. In fact, the middle layer satisfies

```text
|A_3| >= 10,
```

and the frozen bounds then give the candidate lower bound

```text
|F| >= 1+6+12+10+12+6+1 = 48.
```

The proof is for an arbitrary finite trace ground set `U`. It does not use a
fixed core, a bounded search, a uniqueness assertion for the twelve-member
blocker witness, or a uniformity assumption.

The immutable inputs used below are:

* `PROVED`: the canonical seven-layer framework, the all-or-none block `H`,
  the predecessor/successor conditions, and the bounds
  `(1,6,12,9,12,6,1)` from
  `proof/g4.5-coupled-layers/frozen-subproblem.md`;
* `PROVED`: the oriented covering inequality for every internal layer and the
  bounds `|S| >= i` for a small member and `|U\\K| >= 6-i` for a large trace,
  as reconstructed in the frozen G4 global interface;
* `LITERATURE`: finite blocker involution for clutters, as frozen and accepted
  in G4.4;
* `DEFINITION`: finite blockers are inclusion-minimal transversals.

No claim or status file is changed by this candidate. The labels in this file
are mathematical evidence for the later referee gate, not a promotion of the
project status.

## 2. Trace notation and blocker recognition

Fix an internal layer `A_i`, with `i` in `{2,3,4}`. A member disjoint from
`H` is called small and is written as a subset `S` of `U`. A member containing
all of `H` is written `K union H`, with `K subseteq U`; put

```text
S_i = { small traces in A_i },
C_i = { U \ K : K union H is in A_i }.
```

The complement map is a bijection between large members and `C_i` members.
The layer antichain gives, for every `S in S_i` and `C in C_i`,

```text
S intersect C is nonempty.                                      (2.1)
```

Indeed `S subseteq K` would make the two layer members comparable.
Saturation, tested on `R union Q` with `R subseteq U` and a fixed nonempty
proper subset `Q` of `H`, gives the exact oriented cover

```text
for every R subseteq U,
    some S in S_i has S subseteq R,
    or some C in C_i has C intersect R = empty.                 (2.2)
```

The two sides are nonempty. If `S_i` were empty, (2.2) at `R=U` would force
some `C` to be empty, contradicting the internal size bounds. If `C_i` were
empty, (2.2) at `R=empty` would force an empty small member, again a
contradiction.

### Lemma 2.1 (exact blocker pair)

`PROVED`: for each `i` in `{2,3,4}`,

```text
S_i = B(C_i) and C_i = B(S_i).                                (2.3)
```

#### Proof

By (2.1), every member of `S_i` is a transversal of `C_i`. If a proper subset
of `S` were also a transversal, apply (2.2) to that subset. The second option
is impossible because it intersects every `C`; the first option gives a member
of `S_i` properly contained in `S`, contradicting the layer antichain.
Thus every `S` is a minimal transversal.

Conversely, let `T` be a minimal transversal of `C_i`. No `C` is disjoint from
`T`, so (2.2) supplies `S in S_i` with `S subseteq T`. Since `S` is itself a
transversal, minimality of `T` gives `S=T`. Hence `S_i=B(C_i)`.

For the other equality, (2.1) says every `C` is a transversal of `S_i`. Let
`T` be any transversal of `S_i` and put `R=U\T`. No small member is contained
in `R`, because `T` meets every small member. Equation (2.2) then gives
`C in C_i` disjoint from `R`, so `C subseteq T`. Thus every transversal of
`S_i` contains a member of `C_i`. In particular, no proper subset of a member
`C in C_i` can be a transversal: otherwise that subset would contain some
`C' in C_i`, contradicting the `C_i` antichain. Hence every `C in C_i` is a
minimal transversal. Conversely, every minimal transversal contains a member
of `C_i` and must equal it by minimality. Therefore `C_i=B(S_i)`.  `\square`

### Lemma 2.2 (private witnesses and side counts)

`PROVED`: if `T in B(G)` for a finite family `G`, every `x in T` has a
private witness `G_x in G` with `T intersect G_x={x}`. Consequently
`|T| <= |G|`.

#### Proof

`T\{x}` is not a transversal, so some `G_x` misses it. As `T` is a
transversal, its intersection with `G_x` is exactly `{x}`. Two distinct
points cannot use the same witness, which gives an injection from `T` into
`G`. `\square`

For `A_3`, the frozen size restrictions are

```text
|S| >= 3 for S in S_3,       |C| >= 3 for C in C_3.           (2.4)
```

Applying Lemma 2.2 in both directions to (2.3) gives

```text
|S_3| >= 3 and |C_3| >= 3.                                   (2.5)
```

For a finite family `G`, write `tau(G)` for the minimum size of a
transversal. Since every transversal contains a minimal one,

```text
tau(C_3) = min{|S|:S in S_3} >= 3,
tau(S_3) = min{|C|:C in C_3} >= 3.                            (2.6)
```

## 3. Three-row and four-row blocker lemmas

The following lemmas are independent of the layered origin of the families.

### Lemma 3.1 (three rows)

`PROVED`: Let `G={G_1,G_2,G_3}` be a clutter, with `|G_j|>=3` and
`tau(G)>=3`. Then

```text
|B(G)| = |G_1| |G_2| |G_3| >= 27.                            (3.1)
```

#### Proof

If `G_1` and `G_2` meet at `x`, choose any `y in G_3`. The set `{x,y}` (or
the singleton `{x}` when `y=x`) meets all three rows, contradicting
`tau(G)>=3`. Thus the three rows are pairwise disjoint. Choosing one point
from each row gives a transversal, and deleting the chosen point from row
`j` leaves that row unhit. Every such choice is therefore a distinct minimal
transversal. Conversely, a minimal transversal of three disjoint rows contains
exactly one point from each row. This proves the equality in (3.1), and the
product is at least `3^3`. `\square`

### Lemma 3.2 (four rows)

`PROVED`: Let `G={G_1,G_2,G_3,G_4}` be a clutter, with `|G_j|>=3` and
`tau(G)>=3`. Then

```text
|B(G)| >= 6.                                                   (3.2)
```

#### Proof

Form the intersection graph `J` on vertices `1,2,3,4`, joining `j,k` when
`G_j intersect G_k` is nonempty. If `J` contained two vertex-disjoint edges,
choose one intersection point for each edge. Those at most two points hit all
four rows, contradicting `tau(G)>=3`. Thus the matching number of `J` is at
most one.

We use the following complete classification on four vertices. If `J` has no
edge, all four rows are pairwise disjoint. If `J` has at least two edges, take
two edges with a common endpoint `v`. Every other edge must meet both of them;
an edge avoiding `v` can only join their two other endpoints, producing a
triangle. Therefore the graph is one of: a graph with at least two isolated
vertices; a graph with exactly one isolated vertex and a connected
three-vertex component; or a graph with no isolated vertex, which must be the
three-leaf star. The one-edge graph is included in the first case. A triangle
with a fourth vertex joined to any triangle vertex would contain a matching of
size two, so no additional case occurs.

* If there are at least two isolated rows, the isolated rows are disjoint
  from every other row and from each other. Choose one point from each of the
  two isolated rows and extend the choice to a minimal transversal of the
  remaining rows. The disjoint-component blocker product gives at least
  `3*3=9` blockers.

* Suppose exactly one row, say `G_4`, is isolated. Let
  `G'={G_1,G_2,G_3}`. The disjoint-component relation gives
  `tau(G)=tau(G')+1`, so `tau(G')>=2`. The blocker `B(G')` has at least two
  members. To prove this last assertion, if it had one member `T`, the finite
  blocker involution would give `G'=B({T})`; the blocker of a singleton family
  consists only of singleton sets, contradicting `|G_j|>=3`. Hence
  `|B(G)|=|B(G')| |G_4| >= 2*3=6`.

* It remains to consider no isolated row. The graph must be a star with
  center row `G_0` and pairwise disjoint leaves `L_1,L_2,L_3`. Write
  `q_j=|L_j intersect G_0|`, `p_j=|L_j\G_0|`, and
  `c=|G_0\(L_1 union L_2 union L_3)|`. Each `q_j>=1` and
  `p_j+q_j=|L_j|>=3`. The following are distinct minimal transversals:

  1. choose one point from each `L_j`, with at least one chosen point in
     `G_0`; there are `prod_j(p_j+q_j)-prod_j p_j` choices;
  2. choose one point from each `L_j\G_0` and one of the `c` center-only
     points; there are `c prod_j p_j` choices.

  Every listed set hits all rows. Deleting a leaf choice leaves that leaf
  unhit; in the second class deleting the center-only point also leaves the
  center unhit. In the first class, `tau(G)>=3` rules out a proper
  transversal of the three chosen points. Thus all listed sets are minimal,
  and they are disjoint classes. If `c>=1`, their number is at least
  `prod_j|L_j|>=27`. If `c=0`, fix any `j`. Grouping the terms in the first
  product according to whether the chosen point from `L_j` lies in
  `L_j intersect G_0` gives a subcount
  `q_j prod_{k!=j}|L_k| >= 9`. In every graph case the blocker count is at
  least six. `\square`

The one-isolate case uses the finite blocker involution, which is a frozen
G4.4 input. No separate uniqueness claim about the three-row component is
being made.

## 4. The middle equality obstruction

### Proposition 4.1

`PROVED`: `|A_3|` cannot equal `9`; in fact `|A_3|>=10`.

#### Proof

Put `a=|S_3|` and `b=|C_3|`. By (2.5), the only integer splits of
`a+b=9` are

```text
(a,b) in {(3,6),(4,5),(5,4),(6,3)}.                          (4.1)
```

If `b=3`, apply Lemma 3.1 to `C_3`; (2.6) supplies its hypotheses and gives
`a=|B(C_3)|>=27`, contradicting `a=6`. If `b=4`, Lemma 3.2 gives
`a>=6`, contradicting `a=5`.

The remaining two cases are dual. If `a=4`, apply Lemma 3.2 to `S_3` and
use `b=|B(S_3)|`; it gives `b>=6`, contradicting `b=5`. If `a=3`, Lemma
3.1 gives `b>=27`, contradicting `b=6`. Thus no split in (4.1) exists.
Since `a,b` are integers, `a+b>=10`. `\square`

## 5. Coupling audit for A2, A3, and A4

The preceding proposition already excludes total 47. The following
transition lemmas record additional consequences of the shared predecessor /
successor structure. They are not silently used to strengthen the conclusion.

### Lemma 5.1 (large A3 members have small A2 predecessors)

`PROVED`: For every `C in C_3`, there is `S in S_2` with `S intersect C=empty`.
Consequently the corresponding large A3 member has a small predecessor in
`A_2`.

#### Proof

Let `K=U\C`, so `K union H` is in `A_3`. If a small `S in S_2` is contained
in `K`, it has the required relation. Suppose instead that every member of
`S_2` meets `C`. Then `C` is a transversal of `S_2`. The exact blocker pair
for `A_2` gives a `C' in C_2` with `C' subseteq C`. A large predecessor of
`K union H` would give `C subsetneq C''` for some `C'' in C_2`. The two
members `C'` and `C''` of the `C_2` clutter would then be comparable, which
is impossible. Therefore some `S in S_2` misses `C`, and `S subseteq K` is a
strict predecessor relation because the upper member contains `H`. `\square`

### Lemma 5.2 (small A3 members have large A4 successors)

`PROVED`: For every `S in S_3`, there is `C in C_4` with `S intersect C=empty`.
Consequently the corresponding large A4 member is a successor of `S`.

#### Proof

If a large successor already exists, the conclusion holds. Assume no `C in
C_4` is disjoint from `S`. Then `S` is a transversal of `C_4`, so the blocker
pair for `A_4` gives a small `S' in S_4` with `S' subseteq S`. The predecessor
condition for `S'` supplies `S'' in S_3` with `S'' subsetneq S'`. This makes
two members of the antichain `S_3` comparable: if `S''=S`, the strict
inclusion gives `S subsetneq S' subseteq S`; otherwise `S'' subsetneq S`.
Both alternatives are impossible. Hence some `C in C_4` misses `S`, and
`S subseteq U\C` gives the required large successor (strict because it
contains `H`). `\square`

### Equality-side audit

`PROVED`: if `|A_2|=12`, write `a_2=|S_2|`, `b_2=|C_2|`. The frozen G4.4
split estimates include `a_2=5 => b_2>=8` (the five-generator theorem),
`b_2=3 => a_2>=12`, `b_2=2 => a_2>=16`, and `a_2=4 => b_2>=16`.
Together with the private-witness bounds, they leave only

```text
(a_2,b_2) in {(6,6),(7,5),(8,4)}.                            (5.1)
```

The dual transformed interface gives, for `A_4`,

```text
(|S_4|,|C_4|) in {(6,6),(5,7),(4,8)}.                      (5.2)
```

These lists do not assume that any twelve-member blocker pair is isomorphic
to the two-four-cycle witness. Lemmas 5.1 and 5.2 hold for every choice in
(5.1)--(5.2), but Proposition 4.1 makes a further equality classification
unnecessary for the total-47 exclusion.

## 6. Final deduction and evidence boundary

`PROVED` (candidate, pending isolated referee reconstruction): the frozen
endpoint and side bounds, together with Proposition 4.1 and the G4.4 exact
local bound, imply

```text
|F| >= 1+6+12+10+12+6+1 = 48.                              (6.1)
```

Therefore total canonical size 47 cannot occur on any finite ground set in
the frozen stable-range setup. This is an arbitrary-finite-ground-set
argument, not a finite-core extrapolation.

`COMPUTED`: `experiments/g4.5-coupled-layers/check_a3_blocker_lemma.py` was
replayed with the locked Python 3.12.13 environment on all labelled three- and
four-row clutters whose row members have size at least three, for ground sizes
`3,4,5,6`. The two blocker implementations, powerset filtering and
choice-union minimization, agreed on every enumerated clutter. None of those
ground sizes contained a family with
transversal number at least three, so this exhaustive portion does not test
the new lower bounds non-vacuously. The same two implementations separately
checked non-vacuous disjoint-three-row,
four-row-star, and triangle-plus-isolate examples, with blocker counts
`27`, `19`, and `21`. The exact output is recorded in
`finite-check-output.json`. This computation is regression evidence only and
is not a dependency of (6.1). The replay command was

```text
UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run python \
  Problems/P0054/experiments/g4.5-coupled-layers/check_a3_blocker_lemma.py
```

The source hash is
`02ea73cfccb66f826e533add2ee63b200f3340b158453bf7930fc1a4c0b52fa1` and the
saved output hash is
`a74ba94989071063cc12bdca3c713b5d97c54a3f0c9266ab2a28f73627e493d1`.

`REFUTED` (discarded coupling shortcut at the set-relation level): it is not
valid to infer that the choices of an `S_2` disjoint from distinct `C_3`
members in Lemma 5.1 are injective. For example, on
`U={1,2,3,4,5,6}`, the small set `{1,2}` is disjoint from both incomparable
traces `{3,4,5}` and `{3,4,6}`. No injectivity statement is used above. The
first invalid step in that shortcut is the unproved injection assertion. A
separate five-row matching shortcut and its full counterexample are recorded
in `middle-layer-nine-exclusion.md`.

`UNKNOWN`: the exact value of `sat(7)`, uniqueness of equality cases for the
local twelve-member parameter, and whether a different 48-member or larger
construction exists. The candidate does not promote any of these statements.
