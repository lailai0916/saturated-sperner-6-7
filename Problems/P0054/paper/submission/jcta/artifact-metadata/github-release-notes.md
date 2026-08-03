# v1.1.1 — professional manuscript typography refresh

This patch release synchronizes professionally typeset English, JCTA, arXiv,
and Simplified-Chinese manuscript variants for “The exact saturated 6- and
7-Sperner numbers” with the unchanged complete Lean 4 formalization and
certificate payload.

## Principal verified results

- the eventual saturated 6-Sperner number is 30;
- the eventual saturated 7-Sperner number is 55;
- the explicit 55-member construction has small/large split 28/27;
- the analogous complete seven-core layered template class has minimum 56.

The revision improves PDF metadata and bookmarks, adopts portable Chinese
fonts, standardizes tables and title typography, and repairs the JCTA abstract
column layout. It changes no mathematical statement, Lean theorem,
certificate, or computational result.

The archive README distinguishes mathematical proofs, computed discovery
results, and Lean-formalized statements.  Run `verify-integrity.sh` first,
then `verify-core.sh`; use `verify-drat.sh` for the archived DRAT certificates.
Each core replay retains the full transcript and per-step logs and writes
machine-readable `steps.ndjson` and `result.json` summaries containing the
commands, exit codes, Lake warning count, final theorem types, and expected
axiom boundary.

The frozen release package passes all eight core replay steps, including the
Lean, construction, saved-result, and P0054 test checks. Its nine CNF/DRAT
pairs contain 18 verified files. The release asset and checksum sidecar are
published together at GitHub release `v1.1.1` and archived on Zenodo under DOI
`10.5281/zenodo.21769438`. The preceding `v1.1.0` release remains immutable.
