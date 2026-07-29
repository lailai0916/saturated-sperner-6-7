# Public artifact inventory

The provisional full artifact payload is the already verified review archive:

- local path: `output/review/P0054-review-package-2026-07-29.tar.gz`
- SHA-256: `6c1a0227510e903cbf0230574e4e5f89c758e46f7deaa4ffd4dce95ee01ec1cd`
- integrity sidecar:
  `output/review/P0054-review-package-2026-07-29.tar.gz.sha256`

Its top-level verification interface consists of:

- `README.md` and `README.zh-Hans.md`;
- `snapshot.json` and `manifest.sha256`;
- `verify-integrity.sh`;
- `verify-core.sh`;
- `verify-drat.sh`;
- `review-checklist.md`;
- the `repository/` snapshot and its certificate payload.

Before public release, rerun all archive verification entry points and confirm
that the manuscript PDF and submission metadata correspond to the same source
snapshot.  If any byte in the payload changes, mint a new archive and replace
the checksum above before publishing GitHub or Zenodo records.
