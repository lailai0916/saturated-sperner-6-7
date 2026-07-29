# P0054 G4.3 frozen local blocker subproblem

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_3_EIGHT_MEMBER_LAYER_EXCLUSION
NETWORK: OFFLINE
FORMALIZER: FORBIDDEN
PUBLIC_ACTIONS: FORBIDDEN
```

## Definitions

`DEFINITION`: throughout, `U` is an arbitrary finite set and all families are
ordinary finite set families, not multisets. A clutter is an antichain in
`2^U`. A transversal of a family `H` is a subset of `U` meeting every member
of `H`. Its blocker `B(H)` is the clutter of inclusion-minimal transversals.
The empty-family convention is `B(empty family)={empty set}`.

`DEFINITION`: an admissible `(2,4)` blocker pair is a pair of clutters
`(mathcal S,mathcal C)` on `U` satisfying

```text
mathcal S = B(mathcal C),
mathcal C = B(mathcal S),
|S| >= 2 for every S in mathcal S,
|C| >= 4 for every C in mathcal C.
```

Define

```text
m(2,4) = min (|mathcal S| + |mathcal C|)
```

over all admissible pairs on arbitrary finite ground sets.

## Primary theorem candidate

Prove or refute, without bounding `|U|`,

```text
m(2,4) >= 9.
```

Equivalently, rule out every admissible pair with
`a=|mathcal S|`, `b=|mathcal C|`, and `a+b=8`, after separately excluding
smaller totals or importing the already accepted `m(2,4)>=8` local theorem
from the frozen G4.2 candidate.

The required private-witness lemma must be proved explicitly:

```text
if T is in B(H), then every x in T has a witness E_x in H
with T intersect E_x = {x}; distinct x have distinct witnesses;
hence |T| <= |H|.
```

Applied in both directions, it should force `a>=4` and `b>=2`, leaving only

```text
(a,b)=(4,4), (5,3), (6,2).
```

Each split must be handled without assuming the conclusion. The proof must
audit empty sides, nonuniform sizes, repeated incidence patterns, blocker
minimality, and all arbitrary finite `U`.

## Global application boundary

The frozen G4.2 proof already identifies the small generators and complements
of the large traces of `A_2` as mutual blockers, with member-size lower bounds
two and four. Therefore the local theorem would give `|A_2|>=9`.

The complemented side-swap interface sends `A_4` to the same local theorem,
giving `|A_4|>=9`. Together with the accepted frozen layer bounds

```text
(1,6,8,9,8,6,1)
```

and the improved two entries, the proposed dependency-closed sum is

```text
(1,6,9,9,9,6,1), total 41.
```

Finite search is `COMPUTED` only and may not be a proof dependency. Stronger
local exploration (`m>=10,11,12` or a nine-member witness) is forbidden until
the 41 candidate is dependency-closed and later receives two isolated
`ACCEPT` verdicts.
