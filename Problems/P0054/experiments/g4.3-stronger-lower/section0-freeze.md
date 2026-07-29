# P0054 G4.3 Section 0 freeze

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_3_EIGHT_MEMBER_LAYER_EXCLUSION
PRIMARY_TARGET: prove or refute |A2|>=9
GLOBAL_TARGET: prove or refute sat(7)>=41
STRONGER_TARGET: only after a dependency-closed 41 candidate and two ACCEPT verdicts
NETWORK: OFFLINE
FORMALIZER: FORBIDDEN
COMMIT_PUSH_PUBLICATION: FORBIDDEN
STOP_AFTER_GATE: REQUIRED
CAPTURED_AT_UTC: 2026-07-23T01:39:00Z
CAPTURED_AT_LOCAL: 2026-07-22T18:39:00-0700
HEAD: d2c8e3eb81466a3743c736319ef1874920590abc
BRANCH: master
INDEX: EMPTY
SECTION0_VERDICT: PASS
```

## Worktree record before G4.3 writes

`COMPUTED`: `git status --porcelain=v1` had SHA-256
`233b4e234ce01b4e9f5b4ea9117125cd266a49ee4fed2d9c2a380d1bb3cecc8c`.
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
?? p0054-g4.2-stronger-lower-summary.md
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

This is the same dirty-baseline shape recorded by the prior gates, with the
completed G4.2 summary now present. No reset, clean, stash, stage, commit,
checkout, push, or publication action was performed.

## Frozen required proof inputs

| Path | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/status.md` | `4272128056cb89f977377e9915b13d98bca97c143b87e269cf9215c1b5634b6e` |
| `Problems/P0054/claims.yaml` | `d35820b25c181be7c3dc80a95d7d80eefcc6a9260153bd8711cae246c16e037a` |
| `Problems/P0054/proof/g4-global-lower/candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| `Problems/P0054/proof/audits/g4-global-lower/referee-a.md` | `0996bc5bd64941554f3b0e6d36f3d29ffc36a5c1c32e203802092dc81c6acba4` |
| `Problems/P0054/proof/audits/g4-global-lower/referee-b.md` | `b1a40729e21ce51e52739cd5e06cb4417fb7cb399cb43edeffbfdc142852b57a` |
| `Problems/P0054/proof/g4.2-stronger-lower/candidate-proof.md` | `ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e` |
| `Problems/P0054/proof/g4.2-stronger-lower/prover-a-count-classification.md` | `24414500063e4711b97a9c4e83bb068b891a38590cf55ccaed075631048005bb` |
| `Problems/P0054/proof/g4.2-stronger-lower/prover-b-hypergraph-transversal.md` | `8449e6cfac35afe736404a41a22788e8b0537b80cfd2bc24cf7ab3e0534f64ad` |
| `Problems/P0054/proof/g4.2-stronger-lower/prover-c-independent.md` | `45acf9658d2e4371adcdb7e633fafa902e615ded4f359a65baa17f043731fc88` |
| `Problems/P0054/proof/audits/g4.2-stronger-lower/referee-a.md` | `664bdb20b8b9c86fac80a2d2fac654b4b91e95eed2d50512534ea45c88d627a0` |
| `Problems/P0054/proof/audits/g4.2-stronger-lower/referee-b.md` | `5a4866c494d123f6478b2164a314749e5b66f2b92f1ec80db4fb52fca5f79bfc` |
| `p0054-g4.2-stronger-lower-summary.md` | `c198caaad17057cbdd2bc03b0cd0422c9badced70896e326b7aaaf55bb046c02` |

`COMPUTED`: deleting exactly the appended P0054-C18 block from the current
`claims.yaml` reproduces the G4.2 Section 0 hash
`92fd910d59d6f2cd4a4f0b0fd526a77e24a080ed09a288ab676efeb627128564`.
Thus C1--C17 retain their prior bytes; C18 is now frozen together with them.

## G0--G4.2 manifest freeze

All eleven JSON manifests parsed. They total 56,494 bytes. Sorted records of
the form `SHA256 two-spaces path newline` have aggregate digest
`f2fc336f8bbc58b395bae0ae1dbde56d67b9f89dc57a2275686263635141ae0b`.

| Manifest | SHA-256 |
|---|---|
| `Problems/P0054/experiments/certificates/verification-manifest.json` | `090f80066cd3b157f6e29032211ebe4a138e9617dcc785e1ad5687d3548696a5` |
| `Problems/P0054/experiments/core-8-size-55-manifest.json` | `de814a661c5f8f78bf00bdaffc3ed9804e94076637bb3ce4f342374e4a73dc7a` |
| `Problems/P0054/experiments/g4-global-lower/manifest.json` | `a64c6bc7017ba0eddad6709f36e19267194ba3d458c9c5defb92d22a5d562501` |
| `Problems/P0054/experiments/g4.2-stronger-lower/manifest.json` | `67a90d6b9a614f608d3251b9c1d3b86b8b50f96aab9152a04d12c52580c55db6` |
| `Problems/P0054/experiments/size54-g3-layer-bounds/verification-manifest.json` | `15eb4ec0cb2ae00d0612db087bb3e768ab17743b2c0d2eb3a3f5b200515c743a` |
| `Problems/P0054/experiments/size54-g3-profiles/profile-search-manifest.json` | `d4be923bf052a19b3292b36118ff063491442803317a6e90b17d509ef4427b53` |
| `Problems/P0054/experiments/size54-g3-system/complete/verification-manifest.json` | `e101d46c4fab748956056266a3029bd3dbb839c6b692c8e6bd33fd476a4623c8` |
| `Problems/P0054/experiments/size54-g3-system/fixed-middle14/verification-manifest.json` | `1ca447a68e90d13cc60a10af99316acfd7681f60c2cd5c00aeee2d92baa73ebc` |
| `Problems/P0054/formal/witness-table-manifest.json` | `3b726c30669e07e777e4508ddd38015d1fe979c792cd78b32fb0f9f8c5ee09b2` |
| `Problems/P0054/literature/extremal-poset-theory-2026/manifest.json` | `19ef28e11941bc524089c6cdbcd4fb8809bcd2a53f5c99be4d05d8bbbcd34cf5` |
| `Problems/P0054/literature/g4-global-lower/freeze-manifest.json` | `62313da89a38e1a773954956c8252bf7afcd2e841842bc7686a8fd39cae4a62d` |

The G0--G4 manifest subset independently reproduces its prior aggregate
digest `504380abf39eb1430ca25e8a741c027eb6d9dc32e970a9cb16b385b00f542b70`.
The G4 and G4.2 file manifests matched all six listed artifacts byte-for-byte.
The existing G0--G3 manifest regression suite passed 42/42 tests offline.

## Protected-set replay

The old G4.2 Section 0 definition independently reproduced its exact
`182/182` digest
`79b21d761ed6d50877c54c775537d14effcd9c376f2a10ed85f40fa4db8e06ab`.

For G4.3, include every file under `Problems/P0054`, `AGENTS.md`, and all six
root G0--G4.2 summary files; exclude only `status.md`, `claims.yaml`, and paths
inside the three newly authorized G4.3 directories. Before G4.3 writes this
immutable set has:

```text
FILE_COUNT: 195
TOTAL_BYTES: 683250228
SHA256_LINES_DIGEST: c526b9301cc6a42fc84820e6fec332489006cd0c2a60e8a8ddd1a12be7071981
```

The thirteen frozen G4.2 files, including its root summary, total 125,586
bytes and have aggregate digest
`558068835bbc2e9a47932dfdcc88beda74ddbd98135aa469efb416b3c283e325`.

Only the following new paths are writable in this gate:

```text
Problems/P0054/proof/g4.3-stronger-lower/
Problems/P0054/experiments/g4.3-stronger-lower/
Problems/P0054/proof/audits/g4.3-stronger-lower/
p0054-g4.3-stronger-lower-summary.md
```

`status.md` and `claims.yaml` remain read-only until a dependency-closed
candidate has received two isolated `ACCEPT` verdicts. C1--C18 may not be
modified. No Formalizer, network, old size-54 CNF, stage, commit, push,
publication, release, or adjacent gate is authorized.
