# P0054 G4.13 dependency manifest v1

```text
STATUS: VERSION_LOCK_COMPLETE
PRIMARY_DAG: ACYCLIC
STALE_PRIMARY_REFERENCES: 0
LEGACY_ENUMERATIONS_IN_PRIMARY_DAG: 0
FORMAL_PROMOTION: NO
NETWORK: MATHEMATICS_OFFLINE
```

## Scope

This manifest locks the proof dependencies for the G4.13 replacement of the
five-row degree-three subbranch in G4.12 Section 10. It does not replace the
accepted G4.12 candidate, update the formal claim ledger, or assert novelty.

## Dependency order

The primary graph is topologically ordered as follows.

### Layer 0: accepted inputs

- G4.9 supplies the accepted four-row and five-row lower bounds for clutters
  with minimum row size three and transversal number at least three.
- G4.12 supplies the frozen reduction to the five-row degree-three kernel in
  the $(8,8)$ middle split.

### Layer 1: residual foundations

- `p0054_g413_loop_multigraph_lemma.md` is independent.
- `p0054_g413_small_residual_lemmas.md` depends on G4.9.
- `p0054_g413_residual_lemmas_v3.md` depends on the small residual lemmas and
  G4.9.

### Layer 2: kernel lemmas

- `p0054_g413_five_row_pair_lemma_v5.md` depends on all three Layer 1 files.
- `p0054_g413_pair_endpoint_lemma_v2.md` depends only on blocker involution,
  residual identity, and its embedded exact three-row formula.

### Layer 3: pair-graph branches

- `p0054_g413_p4_eight_blocker_lemma_v3.md` depends on the endpoint lemma.
- The P3+K2 branch depends on its projection, full-row, normal-form,
  endpoint-pressure, and residue structural notes.
- `p0054_g413_3k2_pure_projection_v4.md` is self-contained after its
  persistence repair.
- `p0054_g413_remaining_pair_graphs_v2.md` uses residual Lemma 2 only in the
  K1,3 branch; the K3 branch is direct.

### Layer 4: closure

- `p0054_g413_pair_graph_closure_v4.md` depends on the five Layer 3 graph
  exclusions and the exactly-three-pairs conclusion from Layer 2.

No file in an earlier layer depends on a later layer. The primary graph is
acyclic.

## Locked hashes

### Accepted inputs

```text
g4.9/candidate-proof.md=c62752dfc9cdcd4a078f4b1568cd0b1ab046bc4d786a987516cf45e3940f25e1
g4.9/referee-audit.md=de4a3809bbe8de1659794012a7d71c01163ecb62394cd88dd65380e8ccf2e9e0
g4.12/partial-proof.md=34523d981c6f32e03dff873bc488c7b3832341db9459716a1d7058db495ed1ce
g4.12/referee-audit.md=e7b8b468fc6f39f12370c4f46a93d83325d74c50e813f7c566184ede8402eb02
```

### Primary proof artifacts

```text
loop_multigraph_lemma.md=bb618ee9d876cc4f7d6cc281cd8a13fd87dac45f5ab882d8b937fc1905eb5093
small_residual_lemmas.md=dffdd756a2836def930c2e6c672928076ec695d98ce835316937e76c755243b7
residual_lemmas_v3.md=913d35e7100b57d5c0d0e5a0e5ca165c9610daf8f2b507ee485455309f845071
five_row_pair_lemma_v5.md=72166032445a20bf6bc0ed889b21421702ecd8b8b5ea9d85461db3cb8b869334
pair_endpoint_lemma_v2.md=47977370d6e76ffc7d9386f74d930115a079eda5eab7bf00badbc45f04c2ca5d
p4_eight_blocker_lemma_v3.md=bd1eec79e0007269805ad1ec4a52be3501c36f703175e3f2a24e800967cfc06b
p3k2_projection_orbit_audit_v1.md=4673ecdce8bc9f986048786161d552fd05aabd292265c25916fbe4fdf7f095ff
p3k2_upstream_lemma_audit_v1.md=e653d5a366b907aa1c659b783caf23e027f7fc8883f3d75d160bcb37e75d4ed1
p3k2_normal_form_audit_v1.md=ce25131fc7ad2e1e4fd304ca3ea4fd0e696143806d23e91a5b25cda2cef39814
p3k2_endpoint_structural_classifier_v1.md=169d427d7e2c6a517ce068bd6fb6d60a5a3d68a0e19963de36a4ad3d6123e9bf
p3k2_residue_structural_closure_v1.md=c715f52073b9884023a8b479c31c127e107b098d3c903f69c9213b6c978bd843
3k2_pure_projection_v4.md=b859137865547ef3b555d1b2594e26b3442da99cd6ca324705e83126f09be500
remaining_pair_graphs_v2.md=74730c29837daed122efd224edb212c9c84b235b00d0033d251c929f62f26dd7
pair_graph_closure_v4.md=75c9a22128dd6b22937b04b7347ed7ac39533292036409b4fdfeb660efaa5940
```

### Referee artifacts

```text
five_row_pair_referee_audit_v1.md=79b4f058214a6c7972715c2f48e804159538e7082822288e695ed00b8fd53a6f
pair_endpoint_referee_audit_v1.md=2aebcce7a562b5ddb3793f20e533cf552428ac260de323945b73395e0339bfed
p4_referee_closure_v2.md=5249bb3f8bce3629be84d687ccf7fc9f9d54856b9711fb8051882cb608101cdf
p3k2_referee_closure_v1.md=01fececf1f4de64272bc157c3a4228918dbf24d358f0ec5e155736f998b00d2a
3k2_remaining_graphs_referee_v1.md=735a0f433a83c38b12ea0fe92081f7db98c83c31a41d2686bb890fadd106242c
```

## Cross-check boundary

The following objects are not primary proof dependencies:

- the old 24 five-row canonical classes;
- the 33,554,431 active-mask scan;
- the 143 P3+K2 pair-free completions;
- the 11,121 P3+K2 extension states;
- the 125,000 3K2 endpoint assignments;
- both 3K2 11-orbit support tables;
- the K1,3 1,473,276-state projection checker.

Their scripts and outputs remain `COMPUTED` cross-checks.

## Excluded versions

The following versions must not enter any integrated proof:

```text
residual_lemmas_v2.md
five_row_pair_lemma_v4.md
pair_endpoint_lemma_v1.md
p4_eight_blocker_lemma_v2.md
3k2_pure_projection_v3.md
remaining_pair_graphs_v1.md
pair_graph_closure_v3.md
```

They are historical artifacts. Versions 1 and 3 of the endpoint and 3K2
proofs contain the repaired statement and persistence gaps recorded by the
Referee notes.

