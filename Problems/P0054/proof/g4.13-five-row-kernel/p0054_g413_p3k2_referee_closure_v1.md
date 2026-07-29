# P0054 G4.13 P3+K2 final Referee closure v1

```text
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
STATUS: PROVED_CANDIDATE
SCOPE: EIGHT_BLOCKERS_WITH_P3_PLUS_K2_PAIR_GRAPH
COMPUTATION: CROSSCHECK_ONLY
NETWORK: MATHEMATICS_OFFLINE
FORMAL_PROMOTION: NO
```

## Projection classification

For every fixed pair, the endpoint supports on five rows have type `D` or
type `I`. Nonedges of the pair graph impose nonempty intersections between
the corresponding avoidance sets.

The two path edges give exactly five path types. Coupling the independent
edge gives five type-`D` orbits and four type-`I` orbits. Thus there are
exactly nine endpoint projections.

The hand classification is complete. The independent orbit replay finds
1,800 labelled legal tuples and nine orbits whose sizes sum to 1,800.

## Seven projection exclusions

In classes 2, 3, 4, 6, 7, 8, and 9, a path endpoint $x$ misses exactly two
full rows $P,Q$, while its partner $p$ belongs to both.

The endpoint projection gives only the endpoint intersection. The repaired
lemma proves the full statement:

$$
P\cap Q=\{p\}
$$

Any other common point $w$ would make $\{x,w\}$ an extra pair blocker.

The two sets $P\setminus\{p\}$ and $Q\setminus\{p\}$ each have at least two
points. At most one of their four cross-pairs is the fixed pair $\{u,v\}$.
Each other cross-pair yields a minimal blocker with $x$, using $P,Q$ and a
third row as private witnesses. Together with $\{x,p\}$, this forces
$d(x)\ge4$.

Only classes 1 and 5 survive.

## Minimal normal forms

For class 1, the duplicated endpoint rows require exactly one left witness
and one right witness. A third point occurs only as the unique size witness
for the remaining two-point row. Pair legality gives 14 two-point forms and
18 three-point forms.

For class 5, the two endpoint inclusions require either one combined witness
or two separate witnesses. Pair legality gives one one-point form and four
two-point forms.

Repeated supports cannot occur in a deletion-minimal completion. Removing
one twin preserves row size and every incomparability witness. Hence the
32+5 structural list covers arbitrary finite support multisets.

## Endpoint pressure

Three explicit mechanisms exclude 24 class-1 forms and three class-5 forms:

- two special witnesses create two new blockers through the central endpoint
  $p$;
- a path-endpoint fan creates three new blockers through $a$ or $q$;
- an independent-edge fan creates three new blockers through $u$ or $v$.

The private-row witnesses in each displayed blocker were checked directly.
The survivors are eight forms from class 1 and two forms from class 5.

## Residual closure

Nine of the ten survivors have two blockers containing one of the twin
endpoints $a,q$ and sharing another point. Swapping the twin endpoint creates
two more blockers through the shared point. This violates the degree-three
bound.

The last form is the seven-blocker kernel `[1,4]`. The endpoints
$a,q,u,v$ are already saturated. For every restored point support of rank at
most three:

- missing row 1 or 3 forces a new blocker through a saturated endpoint;
- containing rows 1 and 3 together with row 0 creates the pair $\{v,t\}$;
- containing rows 1 and 3 together with row 2 creates the pair $\{u,t\}$;
- the remaining support case creates the blocker $\{t,u,w\}$.

Thus the final kernel is extension-closed inside the degree-three branch.

## Evidence boundary

The 9-orbit, 32+5-form, endpoint-pressure, and residue scripts agree exactly
with the structural proof. The historical 143-completion and 11,121-extension
tables are not primary dependencies.

`FIRST_INVALID_STEP: NONE`.

The P3+K2 pair-graph branch reaches `PROVED_CANDIDATE` for arbitrary finite
ground sets, repeated support patterns, and nonuniform rows.

