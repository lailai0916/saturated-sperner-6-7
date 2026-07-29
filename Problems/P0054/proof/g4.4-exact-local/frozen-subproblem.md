# P0054 G4.4 frozen exact local subproblem

```text
RUN_MODE: EXACT_LOCAL_PARAMETER_DISCOVERY
CURRENT_GATE: P0054_G4_4_EXACT_m_2_4
PRIMARY_TARGET: prove, refute, or exactly determine m(2,4)=12
GLOBAL_TARGET_IF_PROVED: sat(7)>=47
```

## Exact definitions

`DEFINITION`: for a finite set `U` and a set family `mathcal H` on `U`,
`B(mathcal H)` is the family of inclusion-minimal transversals of
`mathcal H`. Families are ordinary set families, not multisets.

`DEFINITION`: an admissible `(2,4)` blocker pair is a pair of clutters
`(mathcal S,mathcal C)` on an arbitrary finite `U` satisfying

```text
mathcal S = B(mathcal C),
mathcal C = B(mathcal S),
min_{S in mathcal S}|S| >= 2,
min_{C in mathcal C}|C| >= 4.
```

`DEFINITION`:

```text
m(2,4)
  = min(|mathcal S|+|mathcal C|)
```

over all admissible pairs and all finite ground sets.

## Frozen evidence

`PROVED`: the accepted G4.3 arbitrary-finite-ground-set theorem gives

```text
m(2,4) >= 9.
```

`PROVED`: the edge clutter of two vertex-disjoint four-cycles and its
four-member blocker gives

```text
m(2,4) <= 12
```

with `|mathcal S|=8`, `|mathcal C|=4`, minimum member sizes two and four,
and both blocker equalities proved directly.

`PROVED`: the strict frozen interval is therefore

```text
9 <= m(2,4) <= 12.
```

`UNKNOWN`: the exact value is not determined by the frozen inputs. The old
post-acceptance exact-eleven exploration was not archived and is not
evidence.

## Exact unresolved splits

Let

```text
a=|mathcal S|, b=|mathcal C|.
```

After the accepted general exclusions, the only unresolved totals below
twelve are:

```text
total 9:  (a,b)=(5,4)

total 10: (a,b)=(6,4), (5,5)

total 11: (a,b)=(7,4), (6,5), (5,6).
```

`DEFINITION`: mutual-blocker duality swaps `(a,b)` and the size thresholds
`(2,4)`. It may avoid recomputing an equivalent oriented search, but every
listed split must still receive an explicit status and explanation.

## Candidate product inequality

`CONJECTURED` at freeze:

```text
|mathcal S||mathcal C| >= 32.                              (P)
```

If (P) is proved for every admissible pair, exact integer arithmetic gives

```text
(a+b)^2 >= 4ab >= 128.
```

Since `11^2=121<128` and `12^2=144>=128`, it follows that
`a+b>=12`. The explicit twelve-member pair would then give `m(2,4)=12`.
No floating-point approximation is needed.

`UNKNOWN`: (P) is not a frozen theorem and must not be used unless proved.
If it is false, the gate must preserve a smallest mechanically verified
counterexample and stop treating (P) as a lemma.

## Priority subproblems

1. `UNKNOWN`: if `|mathcal C|=4`, all `C` have size at least four, and
   `B(mathcal C)` has no singleton, must `|B(mathcal C)|>=8`?
2. `UNKNOWN`: do admissible pairs with splits `(5,5)` or `(6,5)` exist?
3. `UNKNOWN`: can arbitrary finite `U` be reduced to a complete,
   independently checkable finite incidence-pattern/multiplicity theorem?

Every argument must allow arbitrary finite `U`, repeated incidence patterns,
nonuniform member sizes, empty incidence classes, incomparable clutter
members, and counts of actual blocker subsets rather than weighted tuples.

## Result boundary

`DEFINITION`: solver output is `COMPUTED` unless a proved arbitrary-`U`
reduction, an independently checkable exhaustive certificate, and a complete
second implementation together make the computation part of a proof.

`DEFINITION`: only a dependency-closed new local lower bound or exact value
may be sent to the two required isolated offline Referees. Two `ACCEPT`
verdicts are required before P0054-C20, `status.md`, or `claims.yaml` may be
updated.
