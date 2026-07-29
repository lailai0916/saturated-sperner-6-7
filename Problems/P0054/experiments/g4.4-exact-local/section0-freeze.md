# P0054 G4.4 exact-local Section 0 freeze

```text
RUN_MODE: EXACT_LOCAL_PARAMETER_DISCOVERY
CURRENT_GATE: P0054_G4_4_EXACT_m_2_4
PRIMARY_TARGET: prove, refute, or exactly determine m(2,4)=12
GLOBAL_TARGET_IF_PROVED: sat(7)>=47
NETWORK_POLICY: SCOUTS_ONLY_BEFORE_FREEZE
FORMALIZER: FORBIDDEN
COMMIT_PUSH_PUBLICATION: FORBIDDEN
STOP_AFTER_GATE: REQUIRED
FROZEN_AT_UTC: 2026-07-23T03:10:00Z
FROZEN_AT_LOCAL: 2026-07-22T20:10:00-0700
```

## Repository state

```text
HEAD: d2c8e3eb81466a3743c736319ef1874920590abc
BRANCH: master
INDEX: EMPTY
```

The starting `git status --short` was:

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
?? p0054-g4.2-stronger-lower-summary.md
?? p0054-g4.3-stronger-lower-summary.md
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

This is the same dirty-baseline shape recorded by the accepted G4.3 gate.
No reset, clean, stash, checkout, stage, commit, push, publication, or
overwrite action was performed.

## Toolchain

```text
git: 2.55.0
uv: 0.11.29 (Homebrew 2026-07-15 aarch64-apple-darwin)
Python: 3.12.13
pytest: 9.1.1
ruff: 0.15.22
mypy: 2.3.0 compiled
Lean: 4.33.0-rc1 arm64-apple-darwin24.6.0
Lean commit: 62eed1db4d67327ec8120be05f1a1b0847d74561
Lake: 5.0.0-src+62eed1d
Node.js: v22.23.1
jq: 1.8.2
OS: macOS 27.0 build 26A5378n arm64
```

At freeze time the data volume reported 141,647,228 KiB available. The gate
permits at most 30 GB of temporary experiment storage and at most two hours
per split.

## Required old inputs

The following required inputs were read before any G4.4 research role was
started:

- `AGENTS.md`;
- `Problems/P0054/status.md` and `Problems/P0054/claims.yaml`;
- the G4, G4.2, and G4.3 candidate proofs;
- all six corresponding frozen Referee reports;
- `Problems/P0054/proof/g4.3-stronger-lower/stronger-local-parameter.md`;
- all files in `Problems/P0054/experiments/g4.3-stronger-lower/`;
- `p0054-g4.3-stronger-lower-summary.md`;
- all thirteen G0--G4.3 manifest files listed below.

Selected frozen SHA-256 values:

| Path | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/status.md` | `6e957c8a0a195e7fc384f67adf4b9c0ff89034773ebd8254f2cba3822cf5be65` |
| `Problems/P0054/claims.yaml` | `b3f03ea76cddd8af51bb8f5f4e0a6832dd44ae27e1c5d8e4541caeb2afb5536f` |
| G4 `candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| G4 `referee-a.md` | `0996bc5bd64941554f3b0e6d36f3d29ffc36a5c1c32e203802092dc81c6acba4` |
| G4 `referee-b.md` | `b1a40729e21ce51e52739cd5e06cb4417fb7cb399cb43edeffbfdc142852b57a` |
| G4.2 `candidate-proof.md` | `ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e` |
| G4.2 `referee-a.md` | `664bdb20b8b9c86fac80a2d2fac654b4b91e95eed2d50512534ea45c88d627a0` |
| G4.2 `referee-b.md` | `5a4866c494d123f6478b2164a314749e5b66f2b92f1ec80db4fb52fca5f79bfc` |
| G4.3 `candidate-proof.md` | `ff1271a9552f5eaf82f6d44ac19edfa0e5f550d383d2157e0d16b0eac591a684` |
| G4.3 `referee-a.md` | `6e11b6a925c50e9d84f06c53987fb6c527f4fb0567edad5c0602da1d85aba807` |
| G4.3 `referee-b.md` | `22f191ada7e91d9cc00b41eb4011cd0f5a4ad23168aad8b1341c11b4a53c0c84` |
| G4.3 `stronger-local-parameter.md` | `69bdc4575e825e1b49c3de35696e306889cf901d2f2136252033c5c4694e58c9` |
| G4.3 `search.py` | `ce1026519f6e9f7b3a90da6bd0ea7e1eb7fc6d6b0f7db2cadda05262488b7ec0` |
| G4.3 `results.json` | `315a9daea8ab4c1f28e03fdc8d17c1478bdb1ac0a1a28b4ec5fe7bf65b51d095` |
| G4.3 `report.md` | `93084dec2231b05d33fe4d66e585a809261961a0b6a9d10006796f42cfc387fb` |
| G4.3 `manifest.json` | `2f9c604e0c3a7f2bff505acd97f7c1866db44676c1a4a874f62683b386b4b89c` |
| G4.3 `gate-manifest.json` | `6401c98913474973f58db00b0633c8da28b00c16dd2300ff1582437eee3efec8` |
| `p0054-g4.3-stronger-lower-summary.md` | `d7ccb3bfbe6ee06ad795fead19033031449e5deb1963601a0803da8d2e51f562` |

## Manifest and protected-set replay

`COMPUTED`: the G4.3 gate manifest's fifteen listed artifacts matched both
their recorded byte counts and SHA-256 values. In manifest path order their
SHA-256-line aggregate reproduced:

```text
9101a0d12c9e58ff2bfa72c4e9207e11250cc7cbc554f713ec541def6b6e97b2
```

`COMPUTED`: the previous G4.3 protected set independently reproduced:

```text
FILE_COUNT: 195
TOTAL_BYTES: 683250228
SHA256_LINES_DIGEST:
  c526b9301cc6a42fc84820e6fec332489006cd0c2a60e8a8ddd1a12be7071981
```

`COMPUTED`: the thirteen G0--G4.3 JSON manifests all parsed. They total
64,384 bytes and, in lexicographic path order, have aggregate digest:

```text
b90cb7ee7fa41f2bfebf42e30e72c1be0bc78fa35f12b456cc224de705198f2b
```

| Manifest | SHA-256 |
|---|---|
| `Problems/P0054/experiments/certificates/verification-manifest.json` | `090f80066cd3b157f6e29032211ebe4a138e9617dcc785e1ad5687d3548696a5` |
| `Problems/P0054/experiments/core-8-size-55-manifest.json` | `de814a661c5f8f78bf00bdaffc3ed9804e94076637bb3ce4f342374e4a73dc7a` |
| `Problems/P0054/experiments/g4-global-lower/manifest.json` | `a64c6bc7017ba0eddad6709f36e19267194ba3d458c9c5defb92d22a5d562501` |
| `Problems/P0054/experiments/g4.2-stronger-lower/manifest.json` | `67a90d6b9a614f608d3251b9c1d3b86b8b50f96aab9152a04d12c52580c55db6` |
| `Problems/P0054/experiments/g4.3-stronger-lower/gate-manifest.json` | `6401c98913474973f58db00b0633c8da28b00c16dd2300ff1582437eee3efec8` |
| `Problems/P0054/experiments/g4.3-stronger-lower/manifest.json` | `2f9c604e0c3a7f2bff505acd97f7c1866db44676c1a4a874f62683b386b4b89c` |
| `Problems/P0054/experiments/size54-g3-layer-bounds/verification-manifest.json` | `15eb4ec0cb2ae00d0612db087bb3e768ab17743b2c0d2eb3a3f5b200515c743a` |
| `Problems/P0054/experiments/size54-g3-profiles/profile-search-manifest.json` | `d4be923bf052a19b3292b36118ff063491442803317a6e90b17d509ef4427b53` |
| `Problems/P0054/experiments/size54-g3-system/complete/verification-manifest.json` | `e101d46c4fab748956056266a3029bd3dbb839c6b692c8e6bd33fd476a4623c8` |
| `Problems/P0054/experiments/size54-g3-system/fixed-middle14/verification-manifest.json` | `1ca447a68e90d13cc60a10af99316acfd7681f60c2cd5c00aeee2d92baa73ebc` |
| `Problems/P0054/formal/witness-table-manifest.json` | `3b726c30669e07e777e4508ddd38015d1fe979c792cd78b32fb0f9f8c5ee09b2` |
| `Problems/P0054/literature/extremal-poset-theory-2026/manifest.json` | `19ef28e11941bc524089c6cdbcd4fb8809bcd2a53f5c99be4d05d8bbbcd34cf5` |
| `Problems/P0054/literature/g4-global-lower/freeze-manifest.json` | `62313da89a38e1a773954956c8252bf7afcd2e841842bc7686a8fd39cae4a62d` |

For G4.4, protect every pre-existing file under `Problems/P0054`, `AGENTS.md`,
and the seven root G0--G4.3 summary files. Exclude only
`Problems/P0054/status.md`, `Problems/P0054/claims.yaml`, the three authorized
G4.4 directories, and the new G4.4 root summary. Before G4.4 writes this set
has:

```text
FILE_COUNT: 210
TOTAL_BYTES: 683397414
SHA256_LINES_DIGEST:
  cc17227ca98c557f42d3f19eb0a085d6cc7d8f4ed282ebd68ec1dd31331c8f81
```

`status.md` and `claims.yaml` remain conditionally writable only after two
isolated Referees return `ACCEPT`. P0054-C1 through P0054-C19 are immutable.

## P0053 zero-modification baseline

`COMPUTED`: the complete `Problems/P0053` subtree baseline is:

```text
FILE_COUNT: 652
TOTAL_BYTES: 10891371
SHA256_LINES_DIGEST:
  72709eae29a345ddb02888591b3faee15ab01be48170785d65466ae1839a6afe
Problems/P0053/status.md SHA256:
  886bcac67f1c901752f5848c360051f09d35e3090b43e9a785b870dc6ecb1e29
```

The pre-existing P0053 modification belongs to the dirty baseline and must
remain byte-identical throughout this gate.

## Authority boundary

Only these new paths are writable before two `ACCEPT` verdicts:

```text
Problems/P0054/literature/g4.4-exact-local/
Problems/P0054/proof/g4.4-exact-local/
Problems/P0054/experiments/g4.4-exact-local/
Problems/P0054/proof/audits/g4.4-exact-local/
p0054-g4.4-exact-local-summary.md
```

The main agent is the canonical writer. The two Scouts are isolated,
read-only, and are the only roles allowed network access. After the
literature pack is frozen, every remaining role must be offline. No
Formalizer, old size-54 CNF, reset, clean, stage, commit, push, publication,
release, paper rewrite, or adjacent gate is authorized.
