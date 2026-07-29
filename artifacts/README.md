# Frozen artifact archive

Large DRAT proof traces are distributed outside ordinary Git history. Release
`v1.0.0` attaches the complete frozen package:

- `P0054-review-package-2026-07-29.tar.gz`;
- `P0054-review-package-2026-07-29.tar.gz.sha256`.

The expected SHA-256 of the archive is

```text
6c1a0227510e903cbf0230574e4e5f89c758e46f7deaa4ffd4dce95ee01ec1cd
```

The archive contains a fixed repository snapshot, nine CNF/DRAT pairs,
manifests, checksums, and three top-level verification entry points:

```bash
./verify-integrity.sh
./verify-core.sh
./verify-drat.sh /path/to/drat-trim
```

Run `verify-integrity.sh` before using any contained file. `verify-core.sh`
replays the checks that do not require the external DRAT checker.
`verify-drat.sh` checks the archived proof traces with a compatible
`drat-trim`; the exact required revision is recorded in the archive.

The archive is byte-frozen. Its historical status text describes the state at
the moment of the review-package freeze; later publication metadata does not
alter those bytes. The same two files must be used for the GitHub release and
the Zenodo record.

