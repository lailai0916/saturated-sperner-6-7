# JCTA submission package

Status: `LOCAL_PREPUBLICATION_PACKAGE`

This directory contains the editable Journal of Combinatorial Theory,
Series A submission source and the author-facing submission materials for
“The exact saturated 6- and 7-Sperner numbers”.  It is not evidence that the
article or its artifacts have been submitted or made public.

## Principal files

- `manuscript.tex`, `references.bib`: editable Elsevier CAS source.
- `highlights.txt`: five highlights, each no longer than 85 characters.
- `cover-letter.md`: author-confirmed final cover letter.
- `output/doc/P0054-JCTA-cover-letter.docx`: typeset Word version of the
  final cover letter, stored at the repository root relative path.
- `submission-metadata.md`: author and article metadata for the submission
  system.  The telephone number is intentionally omitted from local and
  public files and should be entered directly in the private submission form.
- `data-and-code-availability.md`: finalization checklist for repository and
  archive identifiers.
- `artifact-metadata/`: draft GitHub and Zenodo metadata.
- `submission-output.sha256`: checksums of the five rendered PDF/DOCX outputs.
- `submission-file-map.md`: exact JCTA upload map and exclusions.
- `output/doc/P0054-declaration-of-competing-interests.docx`: separate
  competing-interest statement, stored at the repository root relative path.

## Submission blockers

The following items remain intentionally unresolved:

- publish the curated artifact source on GitHub and create release `v1.0.0`;
- archive the same version on Zenodo and reserve or publish its DOI;
- replace both placeholders in the data-and-code availability statement;
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

Do not submit the package while any URL or DOI placeholder remains in the
manuscript.

## Local build

Run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex
```

The CAS class and bibliography style files are included so that this package
is self-contained.  The repository's ordinary verification commands and the
artifact package's own verification scripts remain authoritative for the
mathematical and computational checks.

## Last local verification

On 29 July 2026, the JCTA source, ordinary English source, and Chinese review
translation compiled to 14, 15, and 16 pages and were visually inspected page
by page.  The complete `lake build` and independent Lean entry point passed,
the forbidden-construct scan was clean, all 178 Python tests passed, and the
fixed review archive passed both its sidecar and internal integrity checks.

Repository-wide Ruff and Mypy still report diagnostics in pre-existing,
untracked certificate-generator scripts; Ruff also repeats those diagnostics
inside the fixed review-package snapshot.  This package does not alter those
user-owned generators.
