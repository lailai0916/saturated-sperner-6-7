# P0054 manuscript

This directory contains the canonical English manuscript and a
Simplified-Chinese review translation for the exact stable values
`sat(6)=30` and `sat(7)=55`. The manuscript was submitted to JCTA on 29 July
2026 as `JCTA-26-00415` and is under editorial review. It has not been accepted
or published, and its bounded-search novelty wording does not claim priority.

## Manuscript files

- `main.tex` — canonical English scholarly source.
- `main.zh-Hans.tex` — faithful Simplified-Chinese reading translation.
- `references.bib` — shared bibliography.
- `../submission/jcta/` — self-contained Elsevier CAS submission source,
  highlights, cover letter, author metadata, declarations, and draft
  GitHub/Zenodo release metadata.

The translation preserves the theorem scope, equations, construction table,
labels, citations, and bibliography of the English source.

## Build the review PDFs

English:

```bash
cd Problems/P0054/paper/manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Simplified Chinese:

```bash
cd Problems/P0054/paper/manuscript
latexmk -lualatex -interaction=nonstopmode -halt-on-error main.zh-Hans.tex
```

The Chinese source uses the TeX Live bundled Fandol typefaces and therefore
does not depend on macOS-only CJK fonts.

The reviewed outputs are installed as:

```text
output/pdf/P0054-sat6-sat7-English.pdf
output/pdf/P0054-sat6-sat7-arXiv-preprint.pdf
output/pdf/P0054-sat6-sat7-zh-Hans.pdf
output/pdf/P0054-sat6-sat7-JCTA-submission-draft.pdf
```

## Reproduce the Lean formalization

From the repository root, build the complete library and the final seven-layer
theorem, then check the independent entry point:

```bash
lake build AiMathLab AiMathLab.P0054Sat7StableExact
lake env lean Problems/P0054/formal/Main.lean
```

The complete exact-value chain first closed on 27 July 2026 and was
revalidated after the anonymous-pre-review revision on 31 July 2026. The
full-library build reported 17,488 successful jobs, and `Main.lean` accepted
both exported theorems:

```text
AiMathLab.P0054.Sat6StableExact.sat_six_eq_thirty
  : IsStableSaturationNumber 6 30
AiMathLab.P0054.Sat7StableExact.sat_seven_eq_fifty_five
  : IsStableSaturationNumber 7 55
```

`IsStableSaturationNumber k s` is a proposition, not a numeric `sat` function
evaluated by Lean. It asserts that some threshold `N` exists such that, for
every `n >= N`, a saturated `k`-Sperner family of size `s` exists on `Fin n`
and every saturated `k`-Sperner family on `Fin n` has size at least `s`.

The pinned environment is Lean 4.33.0-rc1 at commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`, with Mathlib at commit
`79d0395a1825a6264ad5d269e35e60537518955e`.

For both exact theorems, `#print axioms` reports only:

```text
[propext, Classical.choice, Quot.sound]
```

The final Lean sources have zero occurrences of `sorry`, `admit`, an `axiom`
declaration, `unsafe`, `native_decide`, or `run_tac`. The source scan can be
repeated with:

```bash
if rg -n --glob '*.lean' \
  '\b(sorry|admit|axiom|unsafe|native_decide|run_tac)\b' \
  AiMathLab Problems/P0054/formal; then
  echo 'forbidden Lean construct found' >&2
  exit 1
fi
```

For a single replay entry point with persistent logs and a machine-readable
summary, run:

```bash
Problems/P0054/release/verify-core.sh
```

Each run creates a fresh `replay-logs/run.XXXXXX/` directory containing the
complete console transcript, per-step logs, `steps.ndjson`, and `result.json`.
The summary records commands, exit codes, Lake warning count, final theorem
types, and the expected axiom boundary. A deliberately failed Lake command was
also checked to return its nonzero exit code and emit `"status": "FAIL"`.

## Reproduce supporting certificates

Replay the compact 55-member construction verifier:

```bash
uv run python -m scripts.p0054_verify_candidate
```

Replay the exact `m(2,3)` computation:

```bash
UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run --offline python \
  Problems/P0054/experiments/sat6-exact/search.py \
  --verify-results Problems/P0054/experiments/sat6-exact/results.json
```

The large seven-core lower-bound certificate has a separate trust chain and
must not be conflated with the compact 55-member verification; see
`Problems/P0054/paper/supplement/computational-certificate.md`.

## Mathematical and evidential scope

The manuscript contains:

- the exact stable value `sat(6)=30` (`PROVED`, `FORMALIZED`);
- the arbitrary-finite theorem `m(2,3)=9` (`PROVED`, `FORMALIZED`);
- the local theorem `m(2,4)=12` and the bound `sat(7)>=47`
  (`PROVED`, `FORMALIZED`);
- the arbitrary-finite reduction and exhaustive exclusion of every 54-member
  profile (`PROVED`, `FORMALIZED`);
- the exact stable value `sat(7)=55` (`PROVED`, `FORMALIZED`);
- the concrete `Fin 11` certificate for the 55-member construction
  (`FORMALIZED`);
- the composition bound
  `sat(5*j+2+s) <= 2^s*(28^j+27^j)` (`PROVED`);
- certificate-backed optimality only within the seven-core common-block
  layered template class (`PROVED`).

`COMPUTED` results remain supporting evidence unless a proved reduction and
checked certificate connect them to a theorem. `PROVED` records mathematical
arguments and independently checked certificate proofs. `FORMALIZED` records
statements accepted by the Lean kernel. These labels do not imply independent
peer review, novelty, or priority.

The proposed identity `sat(k)=A075529(k)` remains unresolved; in particular,
the manuscript makes no claim about the first unknown case `k=8`.

## Current external state

- JCTA received the manuscript on 29 July 2026 as `JCTA-26-00415`; a request
  to replace the PDFs with the latest exposition-only revision is awaiting a
  human response from Elsevier Researcher Support.
- arXiv submission `7884979` is configured for `math.CO` but remains blocked
  by category endorsement.
- The clean 16-page preprint and upload archive are under
  `output/arxiv/P0054-arxiv-clean-2026-08-03/`. The 16-page Supplement is
  included as ancillary material.
- GitHub release `v1.1.2` and Zenodo DOI `10.5281/zenodo.21770438` identify the
  synchronized manuscript, Lean, certificate, and replay snapshot. The
  preceding `v1.1.0` record remains an immutable historical version.
- After arXiv publication, add its identifier to ORCID, GitHub, Zenodo, and
  the JCTA record through the permitted editorial channel.
