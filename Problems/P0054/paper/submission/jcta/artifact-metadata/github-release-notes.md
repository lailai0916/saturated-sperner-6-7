# v1.0.0 — reproducibility artifacts

This release supports the manuscript “The exact saturated 6- and 7-Sperner
numbers”.  It contains the Lean 4 formalization, exact-search programs,
construction verifiers, certificate generators, CNF instances, DRAT proofs,
verification scripts, manifests, checksums, tests, and locked dependency
metadata.

## Principal verified results

- the eventual saturated 6-Sperner number is 30;
- the eventual saturated 7-Sperner number is 55;
- the explicit 55-member construction has small/large split 28/27;
- the analogous complete seven-core layered template class has minimum 56.

The archive README distinguishes mathematical proofs, computed discovery
results, and Lean-formalized statements.  Run `verify-integrity.sh` first,
then `verify-core.sh`; use `verify-drat.sh` for the archived DRAT certificates.

The release asset and checksum must be attached together.  The matching
Zenodo record has reserved DOI
[`10.5281/zenodo.21679078`](https://doi.org/10.5281/zenodo.21679078).
