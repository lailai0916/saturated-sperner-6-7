# Public artifact inventory

The full artifact payload is the fixed, already verified review archive:

- local path: `output/review/P0054-review-package-2026-07-29.tar.gz`
- exact size: 196,168,454 bytes
- SHA-256: `6c1a0227510e903cbf0230574e4e5f89c758e46f7deaa4ffd4dce95ee01ec1cd`
- Zenodo MD5: `7d08a030d64e8e1ea008f334c15d57c7`
- integrity sidecar:
  `output/review/P0054-review-package-2026-07-29.tar.gz.sha256`
- GitHub release:
  `https://github.com/lailai0916/saturated-sperner-6-7/releases/tag/v1.0.0`
- archival DOI: `10.5281/zenodo.21679078`
- publication date: 29 July 2026

Its top-level verification interface consists of:

- `README.md` and `README.zh-Hans.md`;
- `snapshot.json` and `manifest.sha256`;
- `verify-integrity.sh`;
- `verify-core.sh`;
- `verify-drat.sh`;
- `review-checklist.md`;
- the `repository/` snapshot and its certificate payload.

The GitHub asset reports the SHA-256 above, and Zenodo reports the MD5 above.
The archive sidecar and internal manifest were both verified on 29 July 2026.
The three final PDFs were rebuilt and visually inspected page by page against
the DOI-bearing sources. If any byte in the archive payload changes, mint a new
archive and replace the size and checksum above before publishing a new record.
