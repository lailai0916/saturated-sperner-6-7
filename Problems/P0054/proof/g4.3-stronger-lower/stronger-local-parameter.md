# P0054 G4.3 stronger local-parameter exploration

```text
START_CONDITION: sat(7)>=41 CANDIDATE RECEIVED TWO ACCEPT VERDICTS
SCOPE: ARBITRARY FINITE U
NETWORK: OFFLINE; NOT_USED
FORMALIZER: FORBIDDEN; NOT_USED
FINITE_SEARCH_DEPENDENCY: NONE
EXACT_LOCAL_PARAMETER: UNKNOWN
```

## 1. Strict conclusion

`PROVED`: for the local blocker parameter frozen in this gate,

```text
9 <= m(2,4) <= 12.
```

The lower bound is the dependency-closed arbitrary-finite-`U` theorem in
`candidate-proof.md`, accepted independently by both G4.3 Referees.  The
upper bound is the explicit blocker pair proved below.  Neither direction
uses a finite negative search.

`UNKNOWN`: this exploration does not determine whether the exact value is
9, 10, 11, or 12.

## 2. A twelve-member blocker pair

`DEFINITION`: let

```text
U = {a0,a1,a2,a3,b0,b1,b2,b3}.
```

Let `mathcal S` be the edge clutter of two vertex-disjoint four-cycles:

```text
{a0,a1}, {a1,a2}, {a2,a3}, {a3,a0},
{b0,b1}, {b1,b2}, {b2,b3}, {b3,b0}.
```

Write the two bipartition classes of the first cycle as

```text
A0={a0,a2}, A1={a1,a3},
```

and those of the second as

```text
D0={b0,b2}, D1={b1,b3}.
```

Define

```text
mathcal C = {A0 union D0, A0 union D1, A1 union D0, A1 union D1}.
```

Thus `|mathcal S|=8`, every `S in mathcal S` has size two,
`|mathcal C|=4`, and every `C in mathcal C` has size four.

## 3. Proof that `mathcal C=B(mathcal S)`

`PROVED`: the inclusion-minimal vertex covers of a four-cycle are exactly its
two bipartition classes.

Every vertex cover must meet the two disjoint edges `{a0,a1}` and
`{a2,a3}`, so it has at least two vertices.  A two-vertex cover cannot use
two adjacent vertices, because the opposite edge would be missed.  Hence the
only two-vertex covers are `A0` and `A1`.  Any cover with at least three
vertices contains one of these two opposite pairs and therefore is not
inclusion-minimal.  The same argument gives exactly `D0,D1` for the second
cycle.

`PROVED`: a set is an inclusion-minimal transversal of a disjoint union of
two families exactly when its intersections with the two disjoint ground
parts are inclusion-minimal transversals of the corresponding families.
Meeting the union requires meeting both components.  If either component
intersection were not minimal, deleting a redundant point there would
preserve the global transversal property.  Conversely, deleting any point
from a union of two componentwise minimal transversals makes its component
fail.

It follows that the four unions `Ai union Dj` are exactly the minimal
transversals of `mathcal S`.  Therefore

```text
mathcal C = B(mathcal S).
```

## 4. Direct proof that `mathcal S=B(mathcal C)`

`PROVED`: every edge of either four-cycle meets all four members of
`mathcal C`.  An edge in the first cycle has one endpoint in each of
`A0,A1`, while every member of `mathcal C` contains one whole `Ai`.
The second cycle is identical.  Deleting either endpoint leaves a singleton
that misses the member containing the opposite bipartition class in that
component and either class in the other component.  Hence every member of
`mathcal S` is a minimal transversal of `mathcal C`.

`PROVED`: conversely, let `T` be any transversal of `mathcal C`.  If `T`
meets both `A0` and `A1`, it contains one point from each side of the complete
bipartite graph `C4=K2,2`, hence it contains an edge of the first four-cycle.
If `T` misses one of `A0,A1`, say `Ai`, then meeting both
`Ai union D0` and `Ai union D1` forces `T` to meet both `D0` and `D1`.
It therefore contains an edge of the second four-cycle.

Thus every transversal of `mathcal C` contains a member of `mathcal S`.
Since those eight edges are already minimal transversals, there are no other
members of the blocker, and

```text
mathcal S = B(mathcal C).
```

Consequently this is an admissible pair of total size `8+4=12`, proving
`m(2,4)<=12` on an explicit finite ground set.

## 5. Independent semantic replay

`COMPUTED`: the repository's two independent blocker engines were applied to
the displayed eight-point witness.  The direct powerset engine and the
edge-choice union-minimization engine both returned the four displayed
members of `mathcal C`; applying each engine in the reverse direction
returned the eight displayed members of `mathcal S`.  Both size constraints
were also checked.

```text
SIZE12_WITNESS_VALIDATED_COMPUTED
S=8 C=4 MIN_S=2 MIN_C=4
TWO_VALIDATORS=AGREE INVOLUTION=AGREE
```

The first replay harness attempt failed before validation because the module
loaded through `importlib` had not been inserted into `sys.modules`, which
the `dataclass` decorator required.  The corrected harness inserted the
module before execution and produced the recorded result.  No output from
the failed attempt was used.

## 6. Stronger lower-bound boundary

`PROVED`: the following splits are already excluded by the general arguments
inside the accepted candidate:

- `b=2` implies `a>=16`;
- `b=3` implies `a>=12`;
- `a=4` implies `b>=16`.

`COMPUTED`: the archived incidence-pattern experiment found no pair of total
size 9 or 10.  This remains finite quotient evidence and is not promoted to
a general proof of `m(2,4)>=11`.

`COMPUTED`, not archived as a reproducible artifact and therefore not used as
evidence: a post-acceptance exploratory branch reported zero hits for the
exact-eleven splits `(a,b)=(7,4)` and `(5,6)`.  Its `(6,5)` enumeration was
stopped incomplete.  Because no source, complete parameters, or replayable
output was saved, all exact-eleven splits remain mathematically `UNKNOWN` in
this report.

`UNKNOWN`: an attempted route through the inequality

```text
|mathcal S| |mathcal C| >= 32
```

did not produce a self-contained proof and is not a dependency.  It must not
be cited as a theorem.

After the already proved split exclusions, a proof of the exact value 12
would still have to exclude, by general arbitrary-finite-`U` arguments,

```text
(5,4),
(6,4), (5,5),
(7,4), (6,5), (5,6).
```

The first concrete missing lemma is a proof that four clutter members of
size at least four, with no singleton blocker, always have at least eight
minimal transversals.  Even that lemma would settle only the three splits
with `b=4`; the `b=5,6` cases would remain.

```text
STRONGER_LOCAL_VERDICT: PROVED_INTERVAL_9_TO_12_EXACT_UNKNOWN
GENERAL_LOWER_BOUND_BEYOND_9: UNKNOWN
EXPLICIT_UPPER_WITNESS_SIZE: 12
FINITE_NEGATIVE_RESULTS_USED_AS_PROOF: NO
FIRST_UNRESOLVED_SPLIT: (a,b)=(5,4)
REPOSITORY_WRITES_BY_ISOLATED_PROVER: NONE
```
