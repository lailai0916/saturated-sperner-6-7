# JCTA submission package

Status: `PUBLIC_V1.1_ARTIFACT_VERIFIED_SUBMISSION_PENDING`

This directory contains the editable Journal of Combinatorial Theory,
Series A submission source and the author-facing submission materials for
“The exact saturated 6- and 7-Sperner numbers”.  It is not evidence that the
article or its artifacts have been submitted or made public.

## Principal files

- `manuscript.tex`, `references.bib`: editable Elsevier CAS source.
- `supplement.tex`: editable source for the separately submitted
  “Supplementary proofs and verification dossier”.
- `highlights.txt`: five highlights, each no longer than 85 characters.
- `cover-letter.md`: author-confirmed final cover letter.
- `output/doc/P0054-JCTA-cover-letter.docx`: typeset Word version of the
  final cover letter, stored at the repository root relative path.
- `submission-metadata.md`: author and article metadata for the submission
  system.  The telephone number is intentionally omitted from local and
  public files and should be entered directly in the private submission form.
- `data-and-code-availability.md`: repository and archive identifiers.
- `artifact-metadata/`: draft GitHub and Zenodo metadata.
- `submission-output.sha256`: checksums of the rendered PDF/DOCX outputs.
- `submission-file-map.md`: exact JCTA upload map and exclusions.
- `output/doc/P0054-declaration-of-competing-interests.docx`: separate
  competing-interest statement, stored at the repository root relative path.

## Actions before final approval

GitHub release `v1.1.0` and Zenodo DOI `10.5281/zenodo.21730916` identify the
revision-synchronized artifact. Before approving a journal submission or
arXiv upload, complete the following actions:

- upload the revised editable manuscript source and the Supplement as two
  clearly described items;
- compare the submission system's generated manuscript PDF with the locally
  verified reference PDF;
- verify that the GitHub and Zenodo archives are byte-identical and match the
  published SHA-256 sidecar;
- if Elsevier's submission system requires its declarations tool, complete
  that tool and upload its generated Word document in place of, or together
  with, the locally prepared declaration;
- verify every automatically generated submission-system proof before final
  submission.

The author confirmed on 29 July 2026 that the manuscript has not been
published and is not under consideration elsewhere. The author also reported
that an external specialist review had been completed; no private review
report is archived here, and this is not represented as journal peer review.
The final bibliography and novelty audit is recorded in
`Problems/P0054/literature/final-prepublication-audit-2026-07-29.md`.

## Local build

Run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error supplement.tex
```

The CAS class and bibliography style files are included so that this package
is self-contained.  The repository's ordinary verification commands and the
artifact package's own verification scripts remain authoritative for the
mathematical and computational checks.

## Last local verification

On 30 July 2026, the revised JCTA source, ordinary English source, Chinese
review translation, and Supplement compiled to 16, 17, 17, and 15 pages,
respectively.  The Supplement compiled without warnings.  The JCTA log has
only the known `cas-sc` title-generation box/empty-anchor diagnostics; visual
inspection found no corresponding page overflow.

The fourth-pre-review verification gates passed on the same date:

- the two-target Lake check found all 17,488 jobs current, and the independent
  `Problems/P0054/formal/Main.lean` entry point accepted both exact theorems;
- `#print axioms` reported only `propext`, `Classical.choice`, and
  `Quot.sound`, while the forbidden-construct scan returned zero matches;
- PDF text extraction found no literal `quad`, unresolved references, or
  undefined citations, and every page was visually inspected;
- the revision-matched arXiv source package compiled to the same 16-page PDF;
  and
- the six JCTA submission outputs passed their regenerated SHA-256 manifest.

The authoritative `Problems/P0054/release/verify-core.sh` replay also passed
the same two-target Lake gate, the independent `Main.lean` check,
construction replay, saved-result replay, and 42 P0054 tests. It preserved
full logs and emitted a `PASS` JSON summary with 4,530 nonfatal Lake warnings,
matching theorem types, and the expected axiom boundary. A controlled
failure returned exit code 42 and emitted `FAIL`, rather than a false pass.
The synchronized review-package directory passes `verify-integrity.sh`; its
top-level `verify-core.sh` is byte-identical to the tested authoritative
script. A new default-path empty-cache package replay was not repeated after
this document-only fourth-round change. An external DRAT-trim executable was
not available for a new nine-proof replay; the archive preserves the earlier
independent acceptance logs and states both limitations explicitly.

The supporting Python tests, construction replays, fixed-package integrity
check, and nine archived DRAT replays last passed on 29 July 2026.  Their
sources and certificates were not changed by this document-facing revision.

The hashes in `submission-output.sha256` bind the rendered files containing
the revision DOI and release URL.

Repository-wide Ruff and Mypy still report diagnostics in pre-existing,
untracked certificate-generator scripts; Ruff also repeats those diagnostics
inside the fixed review-package snapshot.  This package does not alter those
user-owned generators.
