# JCTA submission file map

Use this map only after the revision checks in `README.md` are complete.

## Manuscript source upload

- `manuscript.tex`
- `references.bib`
- `cas-sc.cls`
- `cas-common.sty`
- `cas-model2-names.bst`

The local reference PDF is
`output/pdf/P0054-sat6-sat7-JCTA-submission-draft.pdf`.  If the submission
system compiles the source, compare its generated PDF against this local copy
page by page before approval.

## Separate submission items

- Highlights: paste or upload `highlights.txt`.
- Supplementary material: upload `supplement.tex` as editable source and
  `output/pdf/P0054-sat6-sat7-supplement.pdf` as its reference PDF.  Use the
  description “Arbitrary-finite blocker interfaces, a worked finite-domain
  reduction, independent replay counts, and
  theorem--proof--program--Lean crosswalk.”
- Cover letter: `output/doc/P0054-JCTA-cover-letter.docx`.
- Competing interests:
  `output/doc/P0054-declaration-of-competing-interests.docx`; replace or
  supplement it with the document produced by Elsevier's declarations tool if
  the submission system requests that exact form.
- Author metadata: enter the fields from `submission-metadata.md`; enter the
  telephone number directly in the private system.
- Data and code availability: publish GitHub release `v1.1.0` and a new Zenodo
  version, insert the resolving revision URL and version DOI, and verify that
  both identify the exact uploaded snapshot.  The current `v1.0.0` record is
  only the immutable baseline and blocks final approval until superseded in
  the submission files.

## Do not upload as manuscript source

- LaTeX build intermediates (`*.aux`, `*.log`, `*.fls`, `*.fdb_latexmk`,
  `*.out`, `*.blg`, `*.abs`);
- the Simplified-Chinese review translation;
- internal review logs and status files;
- the 447 MB artifact archive as a manuscript-source file.  Host it on the
  GitHub release and Zenodo record, then cite those identifiers in the paper.
