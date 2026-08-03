# Public artifact inventory

Status: `PUBLIC_V1.1.1_PAYLOAD_VERIFIED`

The v1.1.1 payload synchronizes the professionally typeset manuscript with the
unchanged formalization and certificate snapshot. The release archive is:

- local path: `output/release/P0054-artifacts-v1.1.1.tar.gz`
- SHA-256: recorded in the adjacent `.sha256` sidecar after archive creation;
- integrity sidecar:
  `output/release/P0054-artifacts-v1.1.1.tar.gz.sha256`

Its top-level verification interface consists of:

- `README.md` and `README.zh-Hans.md`;
- `snapshot.json` and `manifest.sha256`;
- `verify-integrity.sh`;
- `verify-core.sh`;
- `verify-drat.sh`;
- `review-checklist.md`;
- the `repository/` snapshot and its certificate payload.

The directory payload passes `verify-integrity.sh`. Its top-level
`verify-core.sh` is copied byte-for-byte from
`Problems/P0054/release/verify-core.sh`; that authoritative script passed the
current worktree replay and writes complete logs, `steps.ndjson`, and
`result.json` under a fresh `replay-logs/run.XXXXXX/` directory. The normal
run reported `PASS`; a controlled Lake failure returned 42 and reported
`FAIL`. A new default-path empty-cache replay inside the frozen directory was
not repeated after the fourth-round document-only changes.
`verify-drat.sh` requires an external executable at DRAT-trim commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`; if that checker is unavailable,
the package records this limitation and retains the nine earlier independent
acceptance logs without describing them as a new replay.

The archive and sidecar are published unchanged on GitHub release `v1.1.1`
and Zenodo DOI `10.5281/zenodo.21769438`. If any payload byte changes, it must
be released under a new version rather than replacing these immutable files.
