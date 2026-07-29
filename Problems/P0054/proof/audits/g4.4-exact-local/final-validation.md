# P0054 G4.4 final validation

```text
RUN_MODE: EXACT_LOCAL_PARAMETER_DISCOVERY
CURRENT_GATE: P0054_G4_4_EXACT_m_2_4
VALIDATED_AT_UTC: 2026-07-23T04:50:20Z
HEAD: d2c8e3eb81466a3743c736319ef1874920590abc
RESULT: PASS
```

## Required commands

The main gate ran the required commands from the repository root, with
`~/.elan/env` sourced:

```text
UV_OFFLINE=1 uv sync --locked
  PASS: 22 packages resolved; 20 packages checked

UV_OFFLINE=1 uv run pytest
  PASS: 178 passed in 113.55s

UV_OFFLINE=1 uv run ruff check .
  PASS: All checks passed

UV_OFFLINE=1 uv run mypy scripts tests
  PASS: no issues in 39 source files

lake build
  PASS: 8662 jobs

lake env lean Problems/P0054/formal/Main.lean
  PASS: existing size-55 certificate and expected axiom audit printed

lake env lean Problems/P0001/formal/Main.lean
  PASS: AiMathLab.sum_first_odd printed

git diff --check
  PASS
```

The existing `AiMathLab/P0053Sat7.lean` linter warnings were unchanged
warnings, not command failures.

## Frozen baseline replay

`COMPUTED`: the G4.4 protected set was independently reconstructed after all
authorized status changes:

```text
FILE_COUNT: 210
TOTAL_BYTES: 683397414
SHA256_LINES_DIGEST:
  cc17227ca98c557f42d3f19eb0a085d6cc7d8f4ed282ebd68ec1dd31331c8f81
```

`COMPUTED`: all thirteen G0--G4.3 JSON manifests parsed and reproduced:

```text
FILE_COUNT: 13
TOTAL_BYTES: 64384
SHA256_LINES_DIGEST:
  b90cb7ee7fa41f2bfebf42e30e72c1be0bc78fa35f12b456cc224de705198f2b
```

`COMPUTED`: the complete P0053 subtree remained byte-identical:

```text
FILE_COUNT: 652
TOTAL_BYTES: 10891371
SHA256_LINES_DIGEST:
  72709eae29a345ddb02888591b3faee15ab01be48170785d65466ae1839a6afe
Problems/P0053/status.md SHA256:
  886bcac67f1c901752f5848c360051f09d35e3090b43e9a785b870dc6ecb1e29
```

`COMPUTED`: the reconstructed P0054-C1--C19 prefix SHA-256 remained:

```text
13273c136c6f91154b4418577baab25325a2c9bc7b24554e42e1c33a93236944
```

Only P0054-C20 was appended.  The YAML parsed with the exact ordered claim IDs
P0054-C1 through P0054-C20, and the unresolved list remained exactly
P0054-C5 and P0054-C9.

## New manifests and experiment

All G4.4 JSON files parsed.  Every frozen artifact entry in the literature,
review, and experiment manifests matched its recorded byte count and SHA-256.
The literature and experiment artifact aggregates reproduced respectively:

```text
LITERATURE:
  7b00d14ad2c960698e8d5f36fbff9967cab5fa287336effa4f84d12ed20f7fa6
EXPERIMENT:
  9e12a317debd97ee37f06ed0c4a52db2b9bf39efbae4a4ed17e0bdb55b228601
```

`COMPUTED`: the isolated Experimentalist completed the full deterministic
replay and obtained `STRUCTURAL_REPLAY_MATCH_COMPUTED`.  The main gate
independently reconstructed the canonical stable projection:

```text
995d635cc94b6c28188d60ed866f2e332826a55f3736b54096c2a9bc8f068f4c
```

All 15 totals-9/10/11 rows were `UNSAT_COMPUTED`, had
`complete_exhaustion=true`, had no witness, and had no timeout.  The complete
run recorded 147,340,811 DFS nodes.  No independent exhaustive UNSAT
certificate and no second complete enumerator exist, so none of these outputs
was promoted to `PROVED`.

`COMPUTED`: the two independent blocker implementations agreed on all 199
small clutters in the recorded validation domain.  The incidence formula and
incremental cover engine agreed on 194 nonempty cases.  Both implementations
also independently verified

```text
B(S)=C, B(C)=S, and B(B(S))=S
```

for the twelve-member two-disjoint-four-cycles witness.

## Referee and action boundary

The two frozen compatible Referee reports both end in the allowed verdict
`ACCEPT`; no repair cycle was used.  Their candidate hash remained
`5bacfe8e319ce76ac1c8e8e9efa35fe1454cf896ace8c6ee5c10d8f04b2d9832`.

The dedicated Prover A/B and dedicated Referee A/B role launches failed before
material access because their fixed runtime model was unavailable.  Three
isolated offline compatible Provers, one isolated offline compatible
Experimentalist, and two isolated read-only offline compatible Referees
performed the actual work.  This substitution is recorded rather than counted
as a successful dedicated-role launch.

Final checks confirmed:

- `HEAD` unchanged;
- Git index unchanged and empty of staged G4.4 work;
- no reset, clean, stage, commit, push, publication, or release;
- no Formalizer;
- no post-freeze network use;
- no old size-54 CNF run;
- no G4.4 cache or temporary search file left behind;
- no AI attribution or co-author trailer in G4.4 artifacts;
- P0053 zero modification.

The `FORMALIZED` and novelty-related strings that remain in the pre-existing
status/claims history or in explicit negative evidence boundaries are not new
G4.4 claims.  P0054-C20 is labeled only `PROVED` and contains neither novelty,
priority, `SOLVED`, `FORMALIZED`, nor an exact value of `sat(7)`.
