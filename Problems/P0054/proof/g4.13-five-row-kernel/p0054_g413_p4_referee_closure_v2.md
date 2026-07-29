# P0054 G4.13 P4 final Referee closure v2

```text
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
REVIEWED_ARTIFACT: p0054_g413_p4_eight_blocker_lemma_v3.md
STATUS: PROVED_CANDIDATE
TRACE_CROSSCHECK: COMPUTED_BOUNDED_EXACT_ZERO_COUNTEREXAMPLES
NETWORK: MATHEMATICS_OFFLINE
FORMAL_PROMOTION: NO
```

## Dependency repair

Version 3 binds the central-pair step to the repaired five-blocker corollary
in `p0054_g413_pair_endpoint_lemma_v2.md`. The P4 hypotheses include
$|B(\mathcal H)|=5$, so the corollary applies exactly.

No other mathematical step changed from version 2.

## Structural audit

Let the three pair rows be
$\{a,p\},\{p,q\},\{q,b\}$. The supports of $p,q$ on the five dual rows must
both have size three and meet in one row. Otherwise $\{a,b\}$ becomes a
fourth pair blocker.

The repaired endpoint lemma lets one choose $p$ with
$d_{\mathcal H}(p)=3$. The residual blocker at $p$ has exactly two rows. Its
involution forces:

$$
Y=\{q,c,d\},
\qquad
\{p,b,c\},\{p,b,d\}\in B(\mathcal H)
$$

The symmetric residual forces:

$$
X=\{p,e,f\},
\qquad
\{q,a,e\},\{q,a,f\}\in B(\mathcal H)
$$

The three remaining rows satisfy the two trace conditions and the exact
degree budget of the generalized trace lemma.

That lemma supplies two good blockers $T_1,T_2$. Each lifts to
$T_i\cup\{p,q\}$. Private rows for the trace points remain among the three
central-avoiding rows. Goodness supplies a private row for each of $p,q$.

The two lifted blockers are distinct and contain both central points. They
differ from the four residual blockers containing exactly one central point.
Hence the five-row dual would contain at least six rows.

## Trace audit

The independent trace replay covers all 27 legal role identifications. It
scans every deletion-minimal anonymous support multiset after an exact
multiplicity bound. Its result is:

```text
trace-legal fixed assignments:           1050
fixed assignments needing completion:      12
minimal anonymous completions:              54
minimum good blockers:                       2
counterexamples:                              0
```

The replay is a cross-check. The hand proof remains the primary dependency.

## Verdict

`FIRST_INVALID_STEP: NONE`.

The P4 pair-graph branch reaches `PROVED_CANDIDATE`. No canonical P4 class
table or extension enumeration is a primary proof dependency.

