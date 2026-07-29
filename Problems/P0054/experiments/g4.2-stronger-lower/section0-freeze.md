# P0054 G4.2 Section 0 freeze

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_2_INTERNAL_LAYER_EQUALITY_CLASSIFICATION
PRIMARY_TARGET: sat(7) >= 39
FALLBACK_TARGET: sat(7) >= 38
NETWORK: OFFLINE
FORMALIZER: FORBIDDEN
PUBLICATION_COMMIT_PUSH: FORBIDDEN
STOP_AFTER_GATE: REQUIRED
CAPTURED_AT_UTC: 2026-07-22T17:37:49Z
CAPTURED_AT_LOCAL: 2026-07-22T10:37:49-0700
HEAD: d2c8e3eb81466a3743c736319ef1874920590abc
BRANCH: master
INDEX: EMPTY
SECTION0_VERDICT: PASS
```

## Worktree record before G4.2 writes

`COMPUTED`: `git status --porcelain=v1` had SHA-256
`7bf11cf9355c7b53bafab9143a3d40c8dfd311d683f8191aba9656304e0a4689`.
The pre-existing state was:

```text
 M Problems/P0053/status.md
?? AiMathLab/P0054Size55.lean
?? AiMathLab/P0054Size55Core.lean
?? AiMathLab/P0054Size55WitnessBlocks.lean
?? AiMathLab/P0054Size55WitnessBlocks/
?? Problems/P0053/paper/manuscript/
?? Problems/P0054/
?? f5-p0053-manuscript-draft-summary.md
?? novelty-crosswalk.md
?? output/
?? p0054-f1-size55-formalization-summary.md
?? p0054-f2-manuscript-readiness-summary.md
?? p0054-g0-class-optimality-summary.md
?? p0054-g1-size55-construction-summary.md
?? p0054-g2-size54-discovery-summary.md
?? p0054-g3-structural-lower-bound-summary.md
?? p0054-g4-global-lower-bound-summary.md
?? prior-art-search-log.md
?? proof-audit-summary.md
?? scripts/p0054_generate_lean_witnesses.py
?? scripts/p0054_layered_sat7.py
?? scripts/p0054_size54_discovery.py
?? scripts/p0054_size54_profile_search.py
?? scripts/p0054_size54_structural.py
?? scripts/p0054_size54_system_search.py
?? scripts/p0054_verify_candidate.py
?? scripts/p0054_verify_drat.py
?? submission-readiness-verdict.md
?? tests/test_p0054_drat_manifest.py
?? tests/test_p0054_formalization.py
?? tests/test_p0054_layered_sat7.py
?? tests/test_p0054_size54_discovery.py
?? tests/test_p0054_size54_g3_artifacts.py
?? tests/test_p0054_size54_profile_search.py
?? tests/test_p0054_size54_structural.py
?? tests/test_p0054_size54_system_search.py
```

No reset, clean, stash, stage, commit, checkout, or push was performed.

## Binding control-panel correction

`DEFINITION`: for this G4.2 gate, the published baseline is recorded as the
direct Gerbner et al. general consequence `sat(7)>=9`. Martin--Veldt Theorem
18 is not admitted as a `k=7` baseline because this gate records its applicable
condition as `k>7`. The protected G4 files that previously wrote baseline 10
remain unchanged. This gate-level correction changes neither P0054-C17 nor the
already accepted proof of `sat(7)>=37`.

## Frozen required inputs

| Path | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/statement.md` | `c09275667570ef827939625d7e82560ad8eeb5a448efca3ba251af3208d57990` |
| `Problems/P0054/status.md` | `bc8e3a16b9b14d54200ce95b90c34e77b2c6611e181c3828888d6f0b3f4d0d70` |
| `Problems/P0054/claims.yaml` | `92fd910d59d6f2cd4a4f0b0fd526a77e24a080ed09a288ab676efeb627128564` |
| `Problems/P0054/proof/g4-global-lower/candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| `Problems/P0054/proof/audits/g4-global-lower/referee-a.md` | `0996bc5bd64941554f3b0e6d36f3d29ffc36a5c1c32e203802092dc81c6acba4` |
| `Problems/P0054/proof/audits/g4-global-lower/referee-b.md` | `b1a40729e21ce51e52739cd5e06cb4417fb7cb399cb43edeffbfdc142852b57a` |
| `Problems/P0054/experiments/g4-global-lower/report.md` | `543561c2313001b82846a0a67e30dd711b57664d72a200271b18840eccb3a09d` |
| `p0054-g4-global-lower-bound-summary.md` | `9a5dea3ea97d98a8c35a67ef41b3fcaf4737d0521527f4f8ff7c811dd3bdae84` |

## G0--G4 manifest freeze

`COMPUTED`: all ten manifest files total 55,777 bytes. Sorted lines of the
form `SHA256 two-spaces path newline` have digest
`504380abf39eb1430ca25e8a741c027eb6d9dc32e970a9cb16b385b00f542b70`.

| Manifest | SHA-256 |
|---|---|
| `Problems/P0054/experiments/certificates/verification-manifest.json` | `090f80066cd3b157f6e29032211ebe4a138e9617dcc785e1ad5687d3548696a5` |
| `Problems/P0054/experiments/core-8-size-55-manifest.json` | `de814a661c5f8f78bf00bdaffc3ed9804e94076637bb3ce4f342374e4a73dc7a` |
| `Problems/P0054/experiments/g4-global-lower/manifest.json` | `a64c6bc7017ba0eddad6709f36e19267194ba3d458c9c5defb92d22a5d562501` |
| `Problems/P0054/experiments/size54-g3-layer-bounds/verification-manifest.json` | `15eb4ec0cb2ae00d0612db087bb3e768ab17743b2c0d2eb3a3f5b200515c743a` |
| `Problems/P0054/experiments/size54-g3-profiles/profile-search-manifest.json` | `d4be923bf052a19b3292b36118ff063491442803317a6e90b17d509ef4427b53` |
| `Problems/P0054/experiments/size54-g3-system/complete/verification-manifest.json` | `e101d46c4fab748956056266a3029bd3dbb839c6b692c8e6bd33fd476a4623c8` |
| `Problems/P0054/experiments/size54-g3-system/fixed-middle14/verification-manifest.json` | `1ca447a68e90d13cc60a10af99316acfd7681f60c2cd5c00aeee2d92baa73ebc` |
| `Problems/P0054/formal/witness-table-manifest.json` | `3b726c30669e07e777e4508ddd38015d1fe979c792cd78b32fb0f9f8c5ee09b2` |
| `Problems/P0054/literature/extremal-poset-theory-2026/manifest.json` | `19ef28e11941bc524089c6cdbcd4fb8809bcd2a53f5c99be4d05d8bbbcd34cf5` |
| `Problems/P0054/literature/g4-global-lower/freeze-manifest.json` | `62313da89a38e1a773954956c8252bf7afcd2e841842bc7686a8fd39cae4a62d` |

`COMPUTED`: the G0--G4 manifest regression command passed 42/42 tests:

```text
PYTHONDONTWRITEBYTECODE=1 UV_OFFLINE=1 uv run pytest -p no:cacheprovider \
  tests/test_p0054_drat_manifest.py tests/test_p0054_formalization.py \
  tests/test_p0054_layered_sat7.py tests/test_p0054_size54_discovery.py \
  tests/test_p0054_size54_g3_artifacts.py \
  tests/test_p0054_size54_profile_search.py \
  tests/test_p0054_size54_structural.py \
  tests/test_p0054_size54_system_search.py
```

## Protected-set replay

`COMPUTED`: the pre-G4 baseline replay matched all 160 immutable files; the
two then-authorized historical differences were `status.md` and `claims.yaml`.
The 16 G4 table-listed artifacts matched 16/16.

`COMPUTED`: for the G4.2 immutable set, exclude only `status.md`,
`claims.yaml`, and all paths under the three newly authorized G4.2 directories.
Include every other file under `Problems/P0054`, `AGENTS.md`, and the five
root G0--G4 summary files. The resulting frozen set has:

```text
FILE_COUNT: 182
TOTAL_BYTES: 683124642
SHA256_LINES_DIGEST: 79b21d761ed6d50877c54c775537d14effcd9c376f2a10ed85f40fa4db8e06ab
```

The five frozen summary hashes are:

```text
G0: 6bad6ce3a53e6881f3ecfab31d86dcc51a4ea14d47ea1e3264abe63d896c4a00
G1: 329627ee7cca96768769d6f4143341237ad9425ef95327cf107570ec2ae2f33a
G2: e6c2440935ecf16c3c54a071a52894924df8832ca0a216b7b7daca6314349aa3
G3: da1f4fefc3790f427e7077bae15157c091ea0755042bec3d9c486629b8f101be
G4: 9a5dea3ea97d98a8c35a67ef41b3fcaf4737d0521527f4f8ff7c811dd3bdae84
```

P0054-C1 through P0054-C17 are frozen. Only a dependency-closed stronger
global proof followed by two isolated `ACCEPT` verdicts may authorize adding
P0054-C18 and updating `status.md`/`claims.yaml`.
