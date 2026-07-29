# P0054 G4.8 Isolated Referee Report

```text
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
REVIEWED_COMMIT: 1b6138e531b49b8bad4582fd7886d152376f193d
REVIEWED_TREE: 40c7f76cb4713646f574d7af6be073ec844339d7
CANDIDATE_SHA256: 5bb6f43906a9048cd87a861569d4ed729ab6a2f83bf334943344b1c55dbd09e0
FROZEN_SUBPROBLEM_SHA256: 733cf2f3b847e55ec3ab766b5b2689721211b89a19abdd323a025934cd0d9e87
NETWORK_USED: NO
WORKTREE_MODIFIED: NO
```

All six frozen dependency hashes match the manifest.

## Mathematical verdict

The candidate proves, for arbitrary finite ground sets,

\[
m(3,3)\ge13,
\]

and therefore, relative to the frozen layer interface,

\[
\operatorname{sat}(7)\ge51.
\]

Both remaining total-twelve splits are independently closed:

- `(5,7)`: Lemma 3.1 correctly proves every five-row clutter with row sizes at least three and transversal number at least three has at least eight blockers.
- `(6,6)`: Lemma 4.1 correctly proves the corresponding six-row clutter has at least seven blockers.

## Critical perfect-matching audit

The `|T|=4` residual argument is valid.

Writing

\[
C=B(H)=D\cup\{M,N\},\qquad I=N\cap M,
\]

one has `|I|=1` or `2`.

For `e in I`, each `Q in B(D)` gives `Q union {e}`. Its unique intersection with `M` is `e`; `M` is private for `e`, while private rows in `D` remain private for every point of `Q`. Since `|B(D)|>=3`, this supplies `3|I|` distinct members of `H`.

For `e in M\I`, apply the frozen residual lemma to `C\{M}` after deleting `I`:

- every original row has size at least three;
- `|I|<=2`;
- all residual rows avoid `M`, because `D` avoids `M` and `(N\I) intersect M` is empty;
- hence every residual minimal transversal `P` avoids `M`;
- in `P union {e}`, `M` is private for `e`, and the residual private witnesses of points in `P` do not contain `e`.

These constructions are distinct because their intersection with `M` is the singleton `{e}`. The counts are therefore exactly sufficient:

\[
3+2\cdot2=7\quad(|I|=1),\qquad
2\cdot3+1=7\quad(|I|=2).
\]

The `|T|=5` factorization is also correct: the isolated three-point row `M` forces

\[
6=3|B(C\setminus\{M\})|,
\]

hence two blockers, contradicting the size-at-least-three rows by blocker involution and private witnesses.

## Boundary audit

- Residual families need not remain clutters; taking inclusion-minimal residual rows preserves their blocker.
- Singleton and complete-bipartite blocker inversions are used correctly.
- Loops and parallel actual points are retained, not collapsed.
- Matching-number `0`, `1`, and `2` constructions preserve private vertices and injectivity.
- All constructed transversals are minimal and mutually distinguishable.
- Inactive points, nonuniform row sizes, empty incidence classes, and arbitrary finite ground-set size are covered.
- No computational zero result is used as proof.
- Exact `m(3,3)`, exact `sat(7)`, compatibility at thirteen members, novelty, and priority remain `UNKNOWN`.
- Promotion to `claims.yaml` or `status.md` remains outside this gate.
