# P0054 G4.13 adversarial Referee v1

```text
VERDICT: ACCEPT_AFTER_REPAIRS
FIRST_INVALID_STEP_IN_LOCKED_CHAIN: NONE
AUDITOR: SAME_AGENT_ADVERSARIAL_PASS
PRIMARY_THEOREM: p0054_g413_master_proof_v1.md
STATUS: PROVED_CANDIDATE
LEAN_FORMALIZED: NO
NETWORK: MATHEMATICS_OFFLINE
FORMAL_PROMOTION: NO
```

## Repaired failures

The audit found two genuine defects in superseded versions.

1. `pair_endpoint_lemma_v1.md` omitted the five-blocker hypothesis used to
   turn its lower bound into a contradiction. Version 2 now states the lower
   bound first and the five-blocker corollary explicitly.
2. `3k2_pure_projection_v3.md` used one-point support elimination without
   proving that the blocker persists when other outside points are restored.
   Version 4 adds the restricted-family persistence lemma.

The residual v2 wording also contained one overstrong phrase and one
ambiguous pair-budget sentence. Version 3 repairs both without changing the
mathematics.

All superseded versions are excluded from the dependency manifest.

## Top-level audit

The master proof uses the accepted G4.12 reduction to a five-row kernel
$\mathcal K$ and its blocker $\mathcal H$.

- The five-row lemma forces exactly three pair rows.
- A singleton row of $\mathcal H$ would give a point of
  $\mathcal K$-degree five, so every row of $\mathcal H$ has size at least
  two.
- Blocker involution gives $B(\mathcal H)=\mathcal K$ and
  $\tau(\mathcal H)\ge3$.
- Residual Lemma 2 excludes $3\le|\mathcal H|\le5$.
- The completion lemma is exact: every additional row is a transversal of
  $\mathcal K$ and must contain a pair row of $\mathcal H$.
- For six or seven blockers, the repaired endpoint corollary makes every
  completion violate the degree-three bound.
- For eight blockers, the five simple three-edge pair graphs are exhaustive
  and every graph branch is closed.

No finite classification is used in this top-level implication.

## Replay results

All seven JavaScript cross-checks exited with code 0.

```text
P3+K2 labelled projections:             1800
P3+K2 projection orbits:                    9
P3+K2 upstream split:                 7 + 2
P3+K2 normal forms:                  32 + 5
P3+K2 endpoint split:             24+8, 3+2
P3+K2 normal-form mismatches:               0
3K2 projection classes:                     5
3K2 individually admissible supports:    {R4}
P4 legal role partitions:                  27
P4 trace-legal assignments:              1050
P4 minimal anonymous completions:          54
P4 minimum good blockers:                   2
P4 counterexamples:                         0
```

The residual C++ audit was recompiled with strict warnings. Its output was
byte-identical to the saved result:

```text
SHA-256=146aa628b37319adf86b11f33c9a1c97d42c99d967392808e42c1523af515376
Lemma 1 feasible vectors=294
Lemma 1 hypothesis vectors=24
Lemma 1 row-permutation classes=1
Lemma 1 counterexamples=0
Lemma 2 five-row recursion nodes=4315665
Lemma 2 counterexamples=0
```

The same residual audit was recompiled with AddressSanitizer and
UndefinedBehaviorSanitizer. It completed without a diagnostic and produced
the same SHA-256.

The exact-pair generator was recompiled and reproduced its saved output
byte-for-byte:

```text
SHA-256=9edbc0ca68165a79e36ec08aef49961aa017ab3666020ede6a923e0ae6617540
feasible vectors=1890
blocker histogram=20,470,1400
row-permutation classes=24
```

This classification remains a cross-check only.

The residual small certificate also passed with the required input order:

```text
profile_generator_results.txt
residual_five_row_results.txt
```

## Integrity

All 14 locked primary proof hashes match
`p0054_g413_dependency_manifest_v1.md`. No locked file references a
superseded primary version. The Mathesis repository worktree was not touched.

## Verdict

`FIRST_INVALID_STEP_IN_LOCKED_CHAIN: NONE`.

The G4.13 five-row degree-three subbranch reaches `PROVED_CANDIDATE`. This is
not an independent isolated Referee run, a Lean proof, a formal claim update,
or a novelty review.

