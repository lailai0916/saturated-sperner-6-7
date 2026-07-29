# P0054 G4.10 isolated Referee report

```text
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
REVIEWED_HEAD: 5b35bda08342279db986dca5971434182ee9d2b7
FROZEN_SUBPROBLEM_SHA256: c82b485af00399be79f36be46d8b6cece90dd4828a9a065d148305ea71410db4
CANDIDATE_SHA256: 5525e73d5d25394f2e35bcf051968243fb70597e63daa43e9fc0e773b853d454
NETWORK_USED: NO
WORKTREE_MODIFIED: NO
OLD_TO_NEW_DIFF: TYPOGRAPHY_ONLY_10_CHANGED_LOCATIONS_12_MANUAL_SPACING_COMMANDS_REMOVED_AND_2_TEXT_SPACES_ADDED
```

## 1. Hash rebinding

The previously accepted candidate had SHA-256

```text
6a6ca186d997c0828376f2e8f380d49e0eff05d2f3f54bcd98b62e131260441d
```

The current candidate has SHA-256

```text
5525e73d5d25394f2e35bcf051968243fb70597e63daa43e9fc0e773b853d454
```

I reconstructed the old bytes from the current file and the exact changed
locations. The reconstructed file reproduced the old SHA-256 exactly.

Both files have 630 lines. The old file has 21,286 bytes and the current file
has 21,221 bytes. Exactly ten lines changed:

```text
23, 100, 175, 278, 388, 389, 449, 523, 551, 564
```

The changes remove five `\quad` commands and seven `\qquad` commands. At line
564, `\text{or}` becomes `\text{ or }`, adding two ASCII spaces. After these
twelve command removals and two text-space additions, the files are
byte-identical.

No mathematical symbol, relation, variable, formula number, statement,
quantifier, proof branch, numerical value, or code reference changed.

## 2. Frozen inputs

The frozen subproblem and all seven frozen dependencies match their declared
SHA-256 values:

| Input | SHA-256 |
|---|---|
| `Problems/P0054/proof/g4.4-exact-local/candidate-proof.md` | `5bacfe8e319ce76ac1c8e8e9efa35fe1454cf896ace8c6ee5c10d8f04b2d9832` |
| `Problems/P0054/proof/g4.5-coupled-layers/candidate-proof.md` | `41e957067396f3b83f7db4c6fba89c638ddc3894ca34d0eda804da324220f1bc` |
| `Problems/P0054/proof/g4.5-coupled-layers/referee-audit.md` | `30c7ef69bb620f104bc9c70cf9580c2cc00b227730d8a477a76130a6259c027f` |
| `Problems/P0054/proof/g4.5-coupled-layers/post-referee-validation.md` | `763c98a0d40b22661f45db4c290537a61441141111d82a1a71d940ee46a99c4c` |
| `Problems/P0054/proof/g4.9-middle-thirteen/candidate-proof.md` | `c62752dfc9cdcd4a078f4b1568cd0b1ab046bc4d786a987516cf45e3940f25e1` |
| `Problems/P0054/proof/g4.9-middle-thirteen/referee-audit.md` | `de4a3809bbe8de1659794012a7d71c01163ecb62394cd88dd65380e8ccf2e9e0` |
| `Problems/P0054/proof/g4.9-middle-thirteen/post-referee-validation.md` | `d89b17ae745c68d112eb7d2e66e76d812fbff2fc5261ed071197888c338fef9e` |

The current experiment manifest and report both bind the new candidate hash.

## 3. Mathematical verdict

The previous complete mathematical audit applies unchanged to the rebound
candidate.

- The `(5,9)` and `(6,8)` arbitrary-finite loop-multigraph reductions are
  complete. They preserve loops, parallel actual points, repeated incidence
  patterns, nonuniform row sizes, and empty optional classes.
- The `(7,7)` random-subset argument guarantees a three-point row on one
  blocker side only. The seven-row extension requires a three-point blocker
  and does not require a three-point row in the primary family.
- The point-degree bound, 41 four-row kernel classes, old-point
  distributions, new-point enumeration, and `count>7` pruning are complete.
  Adding an actual point cannot destroy an old minimal transversal.
- All six surviving incidence vectors have seven actual points, point and row
  degree three, and one intersection point for every row pair. They are Fano
  planes, so the frozen self-blocking lemma applies.
- The adjacent-condition equivalence, four-row lemma, seven-edge graph lemma,
  and the three Fano lower-layer split exclusions are valid.
- The global proof uses only the frozen mathematical inputs and the exact
  finite enumerations after proved arbitrary-finite reductions.

Thus the total-52 equality profile is impossible. Relative to the frozen
eventual-stability reduction, the candidate establishes

```text
PROVED_CANDIDATE: sat(7) >= 53
```

## 4. Computation and source audit

I reviewed the current manifest-bound Python source with SHA-256

```text
4dd7168574b9f1e2e0332a4851e46ec2f1215af183de0513aa800373cf025587
```

This source-hash review was performed. It included line-by-line inspection of
the support construction, minimal-cover test, multiplicity enumeration,
perfect-matching condition, weighted blocker count, and branch bounds.

The manifest-bound sources and outputs remain:

| Artifact | SHA-256 |
|---|---|
| `support-multigraph-checker.py` | `4dd7168574b9f1e2e0332a4851e46ec2f1215af183de0513aa800373cf025587` |
| `support-multigraph-results.json` | `bd58fded081a9f704187c4ab972d3be955b268c0f9d8d14f02388c8a4b4fb590` |
| `four-row-kernel.cpp` | `fc4f1504838010e86f661edce849dbf7ae3f42681820bca96d1ff0c66b9daec7` |
| `four-row-kernel-results.txt` | `5cad55dc857e02fadb586c671de68e52903d201c6cb654b54694376fd146bfde` |
| `seven-row-extension.cpp` | `8004d3d39212c1b0ece8255f010553445516317820c880234dbe7173a2bcdf5d` |
| `seven-row-extension-results.txt` | `f222ac792ca96642cc53c0c1b2d6ae58819e2230e665e8b4945ffcf1699cf26f` |

The independent replay reproduced all three saved outputs byte-for-byte. It
returned 41 four-row classes, six valid seven-row vectors, and zero non-Fano
vectors. An independent exhaustive check of the seven-edge graph lemma found
minimum maximal-independent-set count six.

These finite results retain the label `COMPUTED`. They become proof
dependencies only after the proved arbitrary-finite reductions. They do not
independently establish a global lower bound.

## 5. Evidence boundary

Exact `sat(7)`, novelty, priority, and Lean formalization remain `UNKNOWN`.
No claim or status promotion, publication, expert contact, push, or G4.11 work
is included.

The initial and final Git status are identical. They contain only the nine
pre-existing untracked G4.10 candidate and experiment files. The Referee
created no repository file or `__pycache__`.

```text
REPOSITORY_MODIFIED: NO
NETWORK_USED: NO
```
