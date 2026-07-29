# P0054 G4.4B staged-diff reconciliation report

```text
RUN_MODE: ARCHIVE_BASELINE_RECONCILIATION_ONLY
CURRENT_GATE: P0054_G4_4B_1_STAGED_DIFF_RECONCILIATION
START_HEAD: d2c8e3eb81466a3743c736319ef1874920590abc
NETWORK: NOT_USED
STAGE_COMMIT_PUSH_RELEASE: NOT_PERFORMED
MATHEMATICAL_FILES_CHANGED: NO
REAL_INDEX_START_SHA256: c6bfeb12a53ebb9c57b7ffe51d3c4ff5dbeba18457285848d7e9da6b0248f6db
REAL_INDEX_END_SHA256: c6bfeb12a53ebb9c57b7ffe51d3c4ff5dbeba18457285848d7e9da6b0248f6db
CACHED_DIFF_CHECK: PASS_WITH_EXACT_DOCUMENTED_WAIVERS
GATE_VERDICT: BASELINE_RECONCILED_FOR_USER_COMMIT
```

This report corrects the preparation gate's omission: its worktree-oriented
`git diff --check` did not test the exact inventory-driven candidate commit.
The reconciliation was performed only in temporary indexes initialized from
`HEAD`. Outside the three authorized metadata updates and the new waiver, no
existing artifact was modified; nothing was deleted, moved, cleaned, or
regenerated, and the real Git index was not changed. This gate does not enter
G4.4A, G5, manuscript revision, formalization, or a stronger-bound search.

## Epistemic boundary

- `PROVED`: the repository records the current bounds
  \(47 \leq \operatorname{sat}(7) \leq 55\).
- `PROVED`: `P0054-C20` is the finite mutual-blocker theorem and the resulting
  lower bound \( \operatorname{sat}(7)\geq47\).
- `FORMALIZED`: only the pre-existing concrete size-55 construction
  `P0054-C10` has this label.
- `UNKNOWN`: novelty, priority, the exact value of \(\operatorname{sat}(7)\),
  and the two unresolved claims `P0054-C5` and `P0054-C9`.
- `UNKNOWN`: no human expert confirmation is recorded. Specialist proof and
  prior-art review remain human actions.

Nothing in this staged-diff reconciliation gate changes those labels.

## Section 0 independent audit

### Rules and Git state

Both `/Users/lailai/.agents/AGENTS.md` and the repository `AGENTS.md` were read
before writing.

The entry state was:

```text
BRANCH: master
UPSTREAM: NONE
HEAD: d2c8e3eb81466a3743c736319ef1874920590abc
HEAD_TREE: 6a9e1883be04a83b66a418d005fbe071c147fd2a
INDEX_TREE: bdcbfec529eeb9b1037ee4afb757849b5d036bd4
INDEX_SHA256: c6bfeb12a53ebb9c57b7ffe51d3c4ff5dbeba18457285848d7e9da6b0248f6db
STAGED: 223 paths, all A Problems/P0054/...
UNSTAGED_USER_FILE: Problems/P0053/status.md
```

The existing staged P0054 set was present before this gate. It contains all
223 original P0054 files and has a working-tree payload of 683,564,827 bytes.
This gate did not unstage, stage, reset, restore, clean, or otherwise rewrite
the index. The pre-existing `Problems/P0053/status.md` edit was not touched.

The reconciliation gate independently re-read the current state before any
write:

```text
HEAD: d2c8e3eb81466a3743c736319ef1874920590abc
HEAD_TREE: 6a9e1883be04a83b66a418d005fbe071c147fd2a
REAL_INDEX_SHA256:
  c6bfeb12a53ebb9c57b7ffe51d3c4ff5dbeba18457285848d7e9da6b0248f6db
STATUS_PORCELAIN_V2_LINES: 266
STATUS_PORCELAIN_V2_SHA256:
  5ed60a68acd2d7f82638692d240b183a5c461a9c64b2a5908d79163703e89271
```

All Git status reads used `GIT_OPTIONAL_LOCKS=0`. Temporary index operations
also used a temporary object directory with the repository object database as
a read-only alternate, so neither the real index nor the repository object
store was used as the write target.

The 223 original P0054 files were independently frozen before writing:

```text
FILE_COUNT: 223
TOTAL_BYTES: 683564827
SHA256_LINES_DIGEST:
  92224238a51538f0fffa7b83d498cad39097b52a6ba2791406fbb76c33b19e04
```

Each aggregate line is `sha256<TAB>bytes<TAB>repository-relative-path`,
sorted bytewise by path.

### Claims, candidate proof, Referees, and final validation

`claims.yaml` parsed with exactly the ordered IDs `P0054-C1` through
`P0054-C20`; dependencies point only to earlier claim IDs and the unresolved
list is exactly `P0054-C5`, `P0054-C9`.

```text
claims.yaml:
  bytes: 5463
  sha256: 14835deb1514002d1e5368419dd4636bfeb164c343ef853f5692cb0c7f0142e5
C1--C20 raw claim range:
  bytes: 5386
  sha256: 77552b09b804657746e68c85e0bdefbd8afc44fd8428aba19f1661bcf6eaf611
status.md:
  bytes: 14921
  sha256: b8f04391eefc9a39e10a9d4825d377f7f55283c5ee56a279f04e9715612090a6
```

The four candidate proofs have aggregate
`a6212b9dbd8856380df86927172913637ca95cfebfe0c3a085a77740088d7b8a`.
The eight Referee reports have aggregate
`e0ab936178a3c90b856f15c44567159fc53986c0ac05bdd33c0f599fc232ed7a`
and all end with `ACCEPT` and `FIRST_INVALID_STEP: NONE`.

The G4.4-specific protected files are:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `proof/g4.4-exact-local/candidate-proof.md` | 23,291 | `5bacfe8e319ce76ac1c8e8e9efa35fe1454cf896ace8c6ee5c10d8f04b2d9832` |
| `proof/audits/g4.4-exact-local/referee-a.md` | 5,174 | `aa49082f8b5db78556c26f182a41a1736fd85789ed4a708aff60606302f2d2a2` |
| `proof/audits/g4.4-exact-local/referee-b.md` | 5,780 | `9f8de2a7d01485baa9e992993017df41098c166689c361c21c761dde92bb5598` |
| `proof/audits/g4.4-exact-local/final-validation.md` | 4,808 | `0ba8d4b4d1b364c5e0e92643d906f847062475b70e32e29bb31eb2209c91ba48` |
| `proof/audits/g4.4-exact-local/review-freeze.json` | 4,433 | `25a89f111a4a5b1487bbea0a40ca0f738cfacd8dd3b2f55f107f178ab9153149` |

The complete protected selection (claims, status, four candidates, eight
Referees, final validation, and 21 historical manifest/freeze files) is
36 files / 315,821 bytes, aggregate
`ba616f2456593e9bc8d4a376ed78a4a32d76ef688001813ae25752170f89d8df`.

### Historical manifest lineage

The authoritative lineage contains 18 JSON files and three Section 0 Markdown
freeze files. All 18 JSON files parsed.

Schema-aware replay of the JSON lineage found 385 repository or recorded-tool
path/hash records:

```text
MATCH: 379
MISSING: 0
HISTORICAL_SUPERSEDED_STATUS_OR_CLAIMS: 6
OTHER_MISMATCH: 0
```

Replay of the three Markdown hash tables found:

```text
MATCH: 69
MISSING: 0
HISTORICAL_SUPERSEDED_STATUS_OR_CLAIMS: 6
OTHER_MISMATCH: 0
```

The twelve historical differences are not rebaselined: each is an older
`status.md` or `claims.yaml` snapshot superseded by an authorized later gate.
No proof, Lean source, Referee report, experiment, or historical manifest
drifted. In particular, G4.4 `review-freeze.json` currently replays `16/18`;
its two old status/claims entries are superseded by the post-review C20
update. The final G4.4 gate manifest binds current status and claims and
replays `21/21`.

Three G4 literature entries preserve only remote PDF URL digests and no local
bytes, so they cannot be re-downloaded or replayed in this offline gate. Their
recorded historical values were preserved unchanged.

Key independently reconstructed aggregates:

```text
G0--G4.3 manifest set: 13 files / 64384 bytes
  b90cb7ee7fa41f2bfebf42e30e72c1be0bc78fa35f12b456cc224de705198f2b
G4.4 protected set: 210 files / 683397414 bytes
  cc17227ca98c557f42d3f19eb0a085d6cc7d8f4ed282ebd68ec1dd31331c8f81
G4.4 literature freeze: 5/5
  7b00d14ad2c960698e8d5f36fbff9967cab5fa287336effa4f84d12ed20f7fa6
G4.4 experiment artifacts: 10/10
G4.4 three-artifact aggregate:
  9e12a317debd97ee37f06ed0c4a52db2b9bf39efbae4a4ed17e0bdb55b228601
```

## Artifact inventory and Git boundary

The machine-readable inventories are:

- `research-artifact-inventory.json`: every canonical P0054 research file in
  the repository-level scope, classified as `TRACKED_SOURCE`,
  `GENERATED_LARGE`, `LOCAL_LOGS`, or `RELEASE_LATER`;
- `large-artifact-manifest.json`: exact byte count, SHA-256, source/command,
  regeneration boundary, proof-dependency status, and archive disposition for
  every generated or local-output path kept out of ordinary Git history;
- `tracked-whitespace-waivers.json`: one exact record per known cached-diff
  warning, bound by path, line, Git diagnostic, and current whole-file
  SHA-256.

The original `Problems/P0054` subtree classification is:

| Class | Files | Bytes | Ordinary Git |
| --- | ---: | ---: | --- |
| `TRACKED_SOURCE` | 107 | 827,372 | yes |
| `GENERATED_LARGE` | 43 | 246,698,036 | no |
| `LOCAL_LOGS` | 64 | 4,230,502 | no |
| `RELEASE_LATER` | 9 | 431,808,917 | no |

The full canonical scope also includes the already committed P0054 Lean
sources, P0054 Python sources and tests, historical root summaries/audits, two
generated review PDFs, this release directory, the root G4.4B summary, and the
P0054-specific root `.gitignore` block. Final counts and bytes are recorded in
`research-artifact-inventory.json`.

The reconciled inventory contains 296 records: 178 `TRACKED_SOURCE` and the
same 118 large/local/release-later records. The waiver is a small
`TRACKED_SOURCE` record and is deliberately absent from
`large-artifact-manifest.json`.

Volatile `.lake`, `__pycache__`, and `.hypothesis` caches are not
artifact-manifest records. They are already covered by pre-existing global
ignore rules and are summarized under
`excluded_preexisting_global_caches`; binding their per-file hashes would make
the inventory drift under the required build and test commands.

## Large-artifact reproducibility

`large-artifact-manifest.json` binds 118 exact paths / 683,252,522 bytes:

| Class | Files | Bytes |
| --- | ---: | ---: |
| `GENERATED_LARGE` CNF | 43 | 246,698,036 |
| `RELEASE_LATER` DRAT | 9 | 431,808,917 |
| `LOCAL_LOGS` logs/models/PDFs | 66 | 4,745,569 |

`COMPUTED`: all 43 CNFs were independently regenerated in memory from the
current tracked Python and recorded parameters; bytes and SHA-256 matched
`43/43`.

The six CNF/DRAT proof pairs that directly support a current `PROVED` claim
contain 12 files / 438,568,314 bytes:

- core-7 target-55: `P0054-C3` and transitively `P0054-C4`;
- four exact independent layer minima: `P0054-C14`;
- fixed-middle-14 exclusion: `P0054-C15`.

Logs are not logical dependencies. The global lower bounds
`P0054-C17`--`P0054-C20` are combinatorial and do not depend on these solver
artifacts. The nine checked DRAT files and their nine paired CNFs form the
recommended later archive payload: 18 files / 447,114,815 bytes.

CNFs are byte-reproducible from tracked source. DRAT traces are not marked
reproducible from tracked source alone because they require exact external
solver builds and proof-trace bytes are not guaranteed stable. Current DRAT
files therefore remain local, checksum-bound, and recommended for a later
Zenodo/GitHub Release or equivalent immutable archive.

## Scope-limited ignore rules

The root `.gitignore` adds 118 repository-root-anchored, exact file paths:
43 CNFs, nine DRAT files, 56 logs, eight models, and two generated review PDFs.
No global JSON, YAML, Markdown, Lean, TeX, proof, or source pattern was added.
The ignored-path set is required to equal the 118 records in
`large-artifact-manifest.json`.

These rules do not affect artifacts already present in the index. The user
must explicitly remove the pre-existing P0054 staged set before assembling
the safe commit.

## Temporary-index staged-diff reconciliation

The exact `TRACKED_SOURCE` path list was loaded into a temporary index created
from `HEAD`. The initial 177-path candidate had 176 additions and one
modification (`.gitignore`), totaling 1,465,442 raw blob bytes. It passed all
artifact-boundary checks:

| Check | Result |
| --- | ---: |
| `.cnf`, `.drat`, `.log`, or `.model` paths | 0 |
| `output/pdf/P0054-*.pdf` paths | 0 |
| blobs at least 100,000,000 bytes | 0 |
| `Problems/P0053/status.md` | 0 |
| `TRACKED_SOURCE` / large-manifest intersection | 0 |
| missing or duplicate `TRACKED_SOURCE` paths | 0 |

Running `git diff --cached --check` directly on that temporary index returned
exit code 2 and 35 diagnostics. The command itself is not reported as an
unconditional pass. Its 3,937-byte output has SHA-256
`0aa83513a2cd124b4d8af32d6abf5e99ef710795c902d462a2e791964ac72be5`.

| File | Lines | Diagnostic | Current SHA-256 | Classification |
| --- | --- | --- | --- | --- |
| `literature/final-prior-art-audit.md` | 100 | `new blank line at EOF.` | `5c8383bc138193af80a07de737bad18ec55ac54d0825d3daa03e038fdcdf18d4` | historical Section 0 snapshot |
| `literature/g4-global-lower/literature-pack.md` | 149 | `new blank line at EOF.` | `dc4a5258ce5fc4b4d2d2ffa5aeb6d96b51d467b2cf013c1655ca44486d22497c` | frozen literature |
| `literature/g4-global-lower/search-log.md` | 99 | `new blank line at EOF.` | `92eef5bf137c16ec5ce66d652ae421935afe0b3c9b380c4ab2aff4781bf0bc00` | frozen literature |
| `literature/g4-global-lower/source-theorem-matrix.md` | 40 | `new blank line at EOF.` | `fee4fddb9bc0f25cc017e23b2bd7366db9687307c2686270ffa6ff408a20ede0` | frozen literature |
| `literature/reference-verification.md` | 21 | `new blank line at EOF.` | `3c4989c3b4fd9cbf2a4c266fce33c3190fb269a3cad36bb16576e35d786bf8e9` | historical Section 0 snapshot |
| `paper/audits/mock-review.md` | 54, 56, 58, 61, 66, 68, 69, 72, 126, 128, 129, 132, 137, 139, 140, 143, 195, 197, 198, 200, 205, 207, 208, 211, 215, 216, 217, 219 | `trailing whitespace.` | `88b88ba498cbcaaf9623c5e25a96f8f760950bc48649b2b712257c865f124c75` | historical Section 0 snapshot |
| `paper/manuscript/references.bib` | 89 | `new blank line at EOF.` | `16fa03231b9a800a06e639798bbf3bf8035f5b831249396992e59dc171854119` | historical Section 0 snapshot |
| `proof/size-55-construction.md` | 102 | `new blank line at EOF.` | `2b4a41b1af63468875f6c27a479cff02e9094ee1d2da820b1b48a8889742e782` | historical snapshot and protected proof |

The 28 mock-review diagnostics are exactly two ASCII spaces used as Markdown
hard breaks. The other seven files end in exactly two LF bytes. None of these
historical or protected files was edited.

`tracked-whitespace-waivers.json` contains 35 individual records in Git output
order. A warning is covered only if the complete tuple
`(path, line, git_diagnostic, current_sha256)` matches. Coverage requires exact
set equality, no duplicate waiver tuple, an unchanged source-file SHA-256, and
`historical_file || protected_file` for every record. Any mismatch or any new
diagnostic yields `BLOCKED_UNEXPECTED_STAGED_DIFF`.

After adding the waiver and updating only this report, the inventory, and the
root gate summary, the final temporary candidate is:

```text
TEMP_COMMIT_PATHS: 178
TEMP_COMMIT_A: 177
TEMP_COMMIT_M: 1
TEMP_COMMIT_BYTES: 1498682
MAX_BLOB:
  Problems/P0054/release/large-artifact-manifest.json
MAX_BLOB_BYTES: 155789
DISALLOWED_ARTIFACTS: 0
WHITESPACE_WARNINGS: 35
WHITESPACE_WAIVERS: 35
CACHED_DIFF_CHECK: PASS_WITH_EXACT_DOCUMENTED_WAIVERS
```

## Exact user commit procedure

The following commands are recommendations only and were not executed. The
first phase is read-only with respect to the real index and must pass before
the user applies the second phase:

```bash
set -euo pipefail

unset GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES
unset GIT_DIR GIT_WORK_TREE GIT_COMMON_DIR

p0054_expected_head=d2c8e3eb81466a3743c736319ef1874920590abc
p0054_expected_real_index_sha=c6bfeb12a53ebb9c57b7ffe51d3c4ff5dbeba18457285848d7e9da6b0248f6db
p0054_inventory=Problems/P0054/release/research-artifact-inventory.json
p0054_large=Problems/P0054/release/large-artifact-manifest.json
p0054_waivers=Problems/P0054/release/tracked-whitespace-waivers.json
p0054_git_dir=$(GIT_OPTIONAL_LOCKS=0 git rev-parse --absolute-git-dir)

p0054_rgit() {
  GIT_INDEX_FILE="$p0054_git_dir/index" git "$@"
}

test "$(p0054_rgit rev-parse HEAD)" = "$p0054_expected_head"
p0054_real_index_sha=$(shasum -a 256 "$p0054_git_dir/index" | awk '{print $1}')
test "$p0054_real_index_sha" = "$p0054_expected_real_index_sha"
jq empty "$p0054_inventory" "$p0054_large" "$p0054_waivers"

jq -e '
  .schema == "ai-math-lab.p0054.research-artifact-inventory.v1" and
  .inventory_file_count == 296 and
  (.records | length) == 296 and
  .category_totals.TRACKED_SOURCE.file_count == 178 and
  .category_totals.TRACKED_SOURCE.bytes == 1498682 and
  ([.records[] | select(.category == "TRACKED_SOURCE")] | length) == 178 and
  ([.records[] | select(.category == "TRACKED_SOURCE") | .bytes] | add)
    == 1498682
' "$p0054_inventory" > /dev/null

jq -e '
  .schema == "ai-math-lab.p0054.large-artifact-manifest.v1" and
  .artifact_count == 118 and
  (.records | length) == 118 and
  ([.records[].bytes] | add) == .total_bytes
' "$p0054_large" > /dev/null

jq -e '
  .schema == "ai-math-lab.p0054.tracked-whitespace-waivers.v1" and
  .warning_count == 35 and
  .waiver_count == 35 and
  .coverage == "EXACT" and
  .match_policy.mode == "EXACT_SET_EQUALITY" and
  all(.waivers[]; .historical_file or .protected_file) and
  ([.waivers[] | [.path, .line, .git_diagnostic, .current_sha256]]
    | length) == 35 and
  ([.waivers[] | [.path, .line, .git_diagnostic, .current_sha256]]
    | unique | length) == 35 and
  ([.waivers[].id] | unique | length) == 35 and
  all(.waivers[];
    ((.warning_type == "NEW_BLANK_LINE_AT_EOF") and
      (.git_diagnostic == "new blank line at EOF.")) or
    ((.warning_type == "TRAILING_WHITESPACE") and
      (.git_diagnostic == "trailing whitespace.")))
' "$p0054_waivers" > /dev/null

p0054_tmp=$(mktemp -d /tmp/p0054-g44b-user-preflight.XXXXXX)
mkdir -p "$p0054_tmp/objects/info" "$p0054_tmp/objects/pack"

p0054_tgit() {
  GIT_INDEX_FILE="$p0054_tmp/index" \
  GIT_OBJECT_DIRECTORY="$p0054_tmp/objects" \
  GIT_ALTERNATE_OBJECT_DIRECTORIES="$p0054_git_dir/objects" \
  GIT_OPTIONAL_LOCKS=0 \
  git -c core.splitIndex=false -c core.fsmonitor=false "$@"
}

jq -r \
  '.records[] | select(.category == "TRACKED_SOURCE") | .path' \
  "$p0054_inventory" |
LC_ALL=C sort > "$p0054_tmp/tracked.paths"

test "$(wc -l < "$p0054_tmp/tracked.paths" | tr -d ' ')" -eq 178
test "$(shasum -a 256 "$p0054_tmp/tracked.paths" | awk '{print $1}')" = \
  d71ffd849cddc7d29e01838e49f599bb135dc58aa7107137d3f5639eea08f16f

p0054_tgit read-tree "$p0054_expected_head"
p0054_tgit add --pathspec-from-file="$p0054_tmp/tracked.paths"
p0054_tgit diff --cached --name-only "$p0054_expected_head" -- \
  > "$p0054_tmp/names"
p0054_tgit diff --cached --name-status "$p0054_expected_head" -- \
  > "$p0054_tmp/name-status"

test "$(wc -l < "$p0054_tmp/names" | tr -d ' ')" -eq 178
test "$(awk '$1 == "A" {n++} END {print n+0}' "$p0054_tmp/name-status")" -eq 177
test "$(awk '$1 == "M" {n++} END {print n+0}' "$p0054_tmp/name-status")" -eq 1
test "$(grep -Fxc 'Problems/P0053/status.md' "$p0054_tmp/names" || true)" -eq 0

set +e
rg '\.(cnf|drat|log|model)$|^output/pdf/P0054-.*\.pdf$' \
  "$p0054_tmp/names" > "$p0054_tmp/disallowed"
p0054_rg_rc=$?
set -e
test "$p0054_rg_rc" -eq 1

jq -r '.records[].path' "$p0054_large" |
LC_ALL=C sort > "$p0054_tmp/large.paths"
comm -12 "$p0054_tmp/tracked.paths" "$p0054_tmp/large.paths" \
  > "$p0054_tmp/tracked-large.intersection"
test ! -s "$p0054_tmp/tracked-large.intersection"

jq -r '
  .records[] |
  select(.category == "TRACKED_SOURCE") |
  [(.bytes | tostring), (.sha256 // ""), .path] |
  @tsv
' "$p0054_inventory" |
LC_ALL=C sort -t "$(printf '\t')" -k3,3 > "$p0054_tmp/expected-blobs"

: > "$p0054_tmp/actual-blobs"
while IFS= read -r p0054_path; do
  p0054_oid=$(p0054_tgit ls-files -s -- "$p0054_path" | awk '{print $2}')
  p0054_size=$(p0054_tgit cat-file -s "$p0054_oid")
  if test "$p0054_path" = "$p0054_inventory"; then
    p0054_sha=
  else
    p0054_sha=$(p0054_tgit cat-file blob "$p0054_oid" |
      shasum -a 256 | awk '{print $1}')
  fi
  printf '%s\t%s\t%s\n' "$p0054_size" "$p0054_sha" "$p0054_path" \
    >> "$p0054_tmp/actual-blobs"
done < "$p0054_tmp/names"
LC_ALL=C sort -t "$(printf '\t')" -k3,3 "$p0054_tmp/actual-blobs" \
  -o "$p0054_tmp/actual-blobs"
cmp "$p0054_tmp/expected-blobs" "$p0054_tmp/actual-blobs"

test "$(awk -F '\t' '{s += $1} END {printf "%.0f", s}' \
  "$p0054_tmp/actual-blobs")" -eq 1498682
test "$(awk -F '\t' '$1 >= 100000000 {n++} END {print n+0}' \
  "$p0054_tmp/actual-blobs")" -eq 0
LC_ALL=C sort -t "$(printf '\t')" -k1,1nr -k3,3 \
  "$p0054_tmp/actual-blobs" > "$p0054_tmp/blobs-by-size"
IFS="$(printf '\t')" read -r p0054_max_size p0054_max_sha p0054_max_path \
  < "$p0054_tmp/blobs-by-size"
test "$p0054_max_size" -eq 155789
test "$p0054_max_path" = \
  Problems/P0054/release/large-artifact-manifest.json

set +e
LC_ALL=C p0054_tgit -c color.ui=false diff --cached --check \
  "$p0054_expected_head" -- > "$p0054_tmp/diff-check.out" 2>&1
p0054_check_rc=$?
set -e
test "$p0054_check_rc" -eq 2
test "$(shasum -a 256 "$p0054_tmp/diff-check.out" | awk '{print $1}')" = \
  0aa83513a2cd124b4d8af32d6abf5e99ef710795c902d462a2e791964ac72be5

sed -nE '/^.+:[0-9]+: .+\.$/p' "$p0054_tmp/diff-check.out" \
  > "$p0054_tmp/actual-warning-headers"
jq -r '.waivers[] | "\(.path):\(.line): \(.git_diagnostic)"' \
  "$p0054_waivers" > "$p0054_tmp/expected-warning-headers"
cmp "$p0054_tmp/expected-warning-headers" \
  "$p0054_tmp/actual-warning-headers"

jq -r '.waivers[] | [.path, .current_sha256] | @tsv' \
  "$p0054_waivers" |
LC_ALL=C sort -u |
while IFS="$(printf '\t')" read -r p0054_path p0054_expected_sha; do
  p0054_oid=$(p0054_tgit ls-files -s -- "$p0054_path" | awk '{print $2}')
  p0054_actual_sha=$(p0054_tgit cat-file blob "$p0054_oid" |
    shasum -a 256 | awk '{print $1}')
  test "$p0054_actual_sha" = "$p0054_expected_sha"
done

# Only after the complete temporary-index preflight succeeds, recheck the
# immutable starting point immediately before changing the real index.
test "$(p0054_rgit rev-parse HEAD)" = "$p0054_expected_head"
p0054_real_index_sha=$(shasum -a 256 "$p0054_git_dir/index" | awk '{print $1}')
test "$p0054_real_index_sha" = "$p0054_expected_real_index_sha"

p0054_rgit restore --staged --source="$p0054_expected_head" -- Problems/P0054
jq -r \
  '.records[] | select(.category == "TRACKED_SOURCE") | .path' \
  "$p0054_inventory" |
p0054_rgit add --pathspec-from-file=-
test "$(p0054_rgit rev-parse HEAD)" = "$p0054_expected_head"

# Full object IDs and modes in the real delta must equal the audited delta.
p0054_tgit diff --cached --raw --no-abbrev "$p0054_expected_head" -- \
  > "$p0054_tmp/temp.raw"
p0054_rgit diff --cached --raw --no-abbrev "$p0054_expected_head" -- \
  > "$p0054_tmp/real.raw"
cmp "$p0054_tmp/temp.raw" "$p0054_tmp/real.raw"
test "$(p0054_rgit rev-parse HEAD)" = "$p0054_expected_head"
```

Do not run `git add Problems/P0054`. If the starting real-index SHA differs,
if any temporary preflight check fails, or if the final raw deltas differ,
stop without committing and re-run this reconciliation gate.

Exact candidate payload after the safe procedure:

```text
TRACKED_PATHS_DIFFERING_FROM_HEAD: 178
ADDED_PATHS: 177
MODIFIED_PATHS: 1
RAW_BLOB_BYTES: 1498682
MAX_BLOB_BYTES: 155789
```

Recommended commit message:

```text
chore(p0054): establish reproducible G4.4 baseline
```

No authorship trailer or generated-content attribution should be appended.

## Validation

The reconciliation-only post-write validation matrix is:

| Check | Result |
| --- | --- |
| gate-local JSON parse | `PASS`: inventory, large manifest, and waiver |
| inventory file bytes and SHA-256 | `PASS`: 295/295 non-self records; self byte fixed point |
| large manifest bytes and SHA-256 | `PASS`: 118/118; file SHA-256 `7e59e1da...911e0f` |
| exact `.gitignore` / large-manifest equality | `PASS`: 118/118 |
| `TRACKED_SOURCE` / large-manifest intersection | `PASS`: 0 |
| disallowed candidate artifacts | `PASS`: 0 |
| candidate paths and states | `PASS`: 178 paths; 177 A; one M; zero D |
| candidate raw blob bytes | `PASS`: 1498682 |
| candidate maximum blob | `PASS`: 155,789 bytes |
| raw cached-diff command | exit 2 with exactly 35 known diagnostics |
| exact waiver tuple coverage | `PASS`: 35/35, no duplicate or unexpected tuple |
| cached-diff policy result | `PASS_WITH_EXACT_DOCUMENTED_WAIVERS` |
| mathematical/proof/Lean/experiment/claims/status changes | `PASS`: 0 |
| real Git index unchanged | `PASS`: exact SHA-256 `c6bfeb12...8f6db` |

The preceding G4.4B preparation gate recorded the offline Python, Lean, locked
environment, artifact replay, and worktree-diff checks. This reconciliation
gate did not rerun build or test commands because its hard boundary forbids
regenerating existing files and its target is only the inventory-driven
cached-diff baseline. Those prior results remain historical evidence, not
newly executed checks.

The baseline is reconciled for the user-controlled commit procedure above.
The current real index intentionally remains in its original unsafe 683 MB
state; only the audited temporary index represented the safe candidate.
