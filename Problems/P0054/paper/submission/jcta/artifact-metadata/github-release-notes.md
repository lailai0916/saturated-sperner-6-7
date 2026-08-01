# v1.1.0 — revised manuscript and complete formalization artifacts

This release synchronizes the revised manuscript and Supplement for “The exact
saturated 6- and 7-Sperner numbers” with the complete Lean 4 formalization.  It
also contains the exact-search programs, construction verifiers, certificate
generators, CNF instances, DRAT proofs, verification scripts, manifests,
checksums, tests, and locked dependency metadata.

## Principal verified results

- the eventual saturated 6-Sperner number is 30;
- the eventual saturated 7-Sperner number is 55;
- the explicit 55-member construction has small/large split 28/27;
- the analogous complete seven-core layered template class has minimum 56.

The revision clarifies that the named Lean declarations are the primary proof
objects for the largest finite classifications, adds a worked arbitrary-finite
five-row-kernel interface, and repairs the manuscript/Supplement crosswalk.

The archive README distinguishes mathematical proofs, computed discovery
results, and Lean-formalized statements.  Run `verify-integrity.sh` first,
then `verify-core.sh`; use `verify-drat.sh` for the archived DRAT certificates.
Each core replay retains the full transcript and per-step logs and writes
machine-readable `steps.ndjson` and `result.json` summaries containing the
commands, exit codes, Lake warning count, final theorem types, and expected
axiom boundary.

The release directory passes its integrity check. The authoritative core
script passes the Lean, construction, saved-result, and P0054 test replays,
including a controlled failure-path test. The release asset and checksum are
attached together and mirrored unchanged on Zenodo under DOI
[`10.5281/zenodo.21730916`](https://doi.org/10.5281/zenodo.21730916).
