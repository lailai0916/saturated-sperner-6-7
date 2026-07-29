# P0054 G4.12 exact fifty-four enumerations

## Scope

These experiments check the finite kernels proved in Sections 3, 4, 8, 9,
10, and 11 of `proof/g4.12-exact-fifty-four/partial-proof.md`. They do not
impose a finite ground-set bound on the original blocker pairs.

The $(7,6)$ kernel consists of one selected edge on each of the seven Fano
lines. The $(8,5)$ kernel adds one row whose intersection with the Fano points
is independent and whose outside-point multiplicity is bounded by the proved
private-witness inequality.

## Commands

```bash
clang++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.12-exact-fifty-four/fano-adjacency.cpp \
  -o /tmp/p0054-g412-fano-adjacency

/tmp/p0054-g412-fano-adjacency \
  Problems/P0054/experiments/g4.12-exact-fifty-four/fano-adjacency-results.txt

uv run python Problems/P0054/experiments/g4.12-exact-fifty-four/verify.py \
  --reference \
  Problems/P0054/experiments/g4.12-exact-fifty-four/fano-adjacency-results.txt \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/verification.json

clang++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.12-exact-fifty-four/middle-six-ten.cpp \
  -o /tmp/p0054-g412-middle-six-ten

/tmp/p0054-g412-middle-six-ten \
  Problems/P0054/experiments/g4.12-exact-fifty-four/middle-six-ten-results.txt

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/verify-middle-six-ten.py \
  --reference \
  Problems/P0054/experiments/g4.12-exact-fifty-four/middle-six-ten-results.txt \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/middle-six-ten-verification.json

clang++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.12-exact-fifty-four/middle-six-ten-low-degree.cpp \
  -o /tmp/p0054-g412-middle-six-ten-low-degree

/tmp/p0054-g412-middle-six-ten-low-degree \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-six-ten-low-degree-results.txt

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-six-ten-low-degree.py \
  --reference \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-six-ten-low-degree-results.txt \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-six-ten-low-degree-verification.json

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/middle-four-row-kernels.py \
  --max-row-size 8 --max-blockers 8 --max-pair-blockers 4 \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-eight-eight-four-row-kernels.json

clang++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-eight-eight-five-row.cpp \
  -o /tmp/p0054-g412-middle-eight-eight-five-row

/tmp/p0054-g412-middle-eight-eight-five-row \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-eight-eight-five-row-results.txt

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-eight-eight-extension.py \
  --four-row-kernels \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-eight-eight-four-row-kernels.json \
  --five-row-kernels \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-eight-eight-five-row-results.txt \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-eight-eight-extension-verification.json

clang++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-four-row.cpp \
  -o /tmp/p0054-g412-middle-seven-nine-four-row

/tmp/p0054-g412-middle-seven-nine-four-row \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-four-row-results.txt

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/middle-four-row-kernels.py \
  --max-row-size 9 --max-blockers 9 --max-pair-blockers 4 \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-four-row-kernels.json

clang++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-extension.cpp \
  -o /tmp/p0054-g412-middle-seven-nine-extension

/tmp/p0054-g412-middle-seven-nine-extension \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-four-row-results.txt \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-extension-results.txt

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-extension.py \
  --kernels \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-four-row-kernels.json \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-extension-verification.json

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-five-row.py \
  --reference \
  Problems/P0054/experiments/g4.11-coupled-fifty-three/\
five-row-kernel-results.txt \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-five-row-verification.json

clang++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-six-row.cpp \
  -o /tmp/p0054-g412-middle-seven-nine-six-row

/tmp/p0054-g412-middle-seven-nine-six-row \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-six-row-results.txt

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-six-row.py \
  --reference \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-six-row-results.txt \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-six-row-verification.json

uv run python \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
verify-middle-seven-nine.py \
  --cpp-kernels \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-four-row-results.txt \
  --python-kernels \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-four-row-kernels.json \
  --cpp-extensions \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-extension-results.txt \
  --python-extensions \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-extension-verification.json \
  --five-row \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-five-row-verification.json \
  --six-row \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-six-row-verification.json \
  --output \
  Problems/P0054/experiments/g4.12-exact-fifty-four/\
middle-seven-nine-cross-verification.json
```

## Implementations

The C++ enumerator generates the candidate family in the exact formula from
the proof and then minimizes it. The Python verifier uses a separate route:
it directly enumerates the internal blockers on the seven Fano points and
adds each outside actual point only to base covers that avoid the added row's
Fano trace.

Both implementations retain parallel outside actual points as distinct
choices. They agree on every summary field.

The degree-three $(6,10)$ checker enumerates the exact four-row incidence
kernel from Section 8. The independent implementation expands actual points
before recomputing all blockers and extension patterns.

The low-degree $(6,10)$ implementations independently enumerate all
loop-multigraph support multiplicities. Neither applies the row-clutter filter
when establishing the lower bound, so the checked domain contains every
inclusion-minimal core from Section 9.

For $(8,8)$, the four-row script enumerates all proper support patterns. The
five-row C++ program enumerates all rank-at-most-three support patterns. The
extension verifier reconstructs actual points and uses iterative choice-union
minimization rather than the support-cover counting formulas.

For $(7,9)$, independent C++ and Python implementations enumerate the
four-row kernels and the full nine-row extensions. The two-row extension
keeps separate fresh-private multiplicities and a fresh-shared multiplicity.
The five-row check replays the frozen G4.11 classes. The six-row programs use
different implementations of the three-row marginal classification and the
cross-side actual-point matching.

## Results

```text
fano_graphs=2187
split_7_6_admissible=1011
split_7_6_blockers_7=24
split_7_6_blockers_8=903
split_7_6_blockers_9=84
split_7_6_target_hits=0
split_8_5_candidates=249576
split_8_5_five_blockers=8400
split_8_5_five_minimum_3=8400
split_8_5_admissible=173304
split_8_5_target_hits=0
```

The complete blocker-count histogram for the admissible $(8,5)$ kernels is
saved in `fano-adjacency-results.txt` and independently reproduced in
`verification.json`.

### The split $(6,10)$

The arbitrary-finite degree reduction first excludes degrees six and five by
the minimum transversal size. At degree four, the two rows avoiding the point
are disjoint. Their $3\times3$ choices give at least nine minimal blockers
containing the point, while the residual clutter supplies at least two blockers
avoiding it. This contradicts the ten-row blocker side. The remaining branches
are degree three and degree at most two.

The degree-three kernel output is:

```text
supports=14
minimal_support_covers=48
active_masks_checked=16383
support_feasible_masks=1064
multiplicity_vectors=95
row_permutation_classes=9
compatible_extensions=0
```

For the low-degree branch, the minimum numbers of minimal edge covers are:

| Degree-three vertices | Vectors | Minimum blockers |
|---:|---:|---:|
| 4 | 5244 | 24 |
| 5 | 57080 | 21 |
| 6 | 44288 | 15 |

The C++ and Python summaries agree on the full matching-number histograms,
the vector counts, and all minima. No possible core has ten blockers.

### The split $(8,8)$

The four-row stage has 49 vectors in four row-permutation classes. Its blocker
profiles are one vector with $(7,3)$ and 48 vectors with $(8,4)$, where the
second coordinate counts pair blockers. The extension checker tests 1432
candidates and finds zero valid extensions.

The five-row stage checks $2^{25}-1=33554431$ active support masks and gives:

```text
support_feasible_masks=96148
multiplicity_vectors=1890
blockers_6_pairs_3=20
blockers_7_pairs_3=470
blockers_8_pairs_3=1400
row_permutation_classes=24
```

The exact extension counts are:

```text
kernel_classes=24
extension_candidates=2514
valid_extensions=0
```

### The split $(7,9)$

The four-row kernel classification is:

```text
active_masks_checked=16383
support_feasible_masks=1592
multiplicity_vectors=136
row_permutation_classes=11
```

Its blocker profiles are:

| Blockers | Pair blockers | Vectors |
|---:|---:|---:|
| 7 | 3 | 1 |
| 8 | 4 | 48 |
| 9 | 3 | 12 |
| 9 | 4 | 75 |

The independent semantic extension counts agree per class and in total:

```text
extension_candidates=138161
valid_extensions=0
```

The frozen five-row replay has 490 vectors in eight classes. Every class has
a three-point row, so none meets the required row-size minimum four.

For the six-row residual kernel, the exact marginal and coupling counts are:

```text
marginal_labelled_solutions=19
marginal_row_permutation_classes=6
labelled_couplings=90898
minimum_pair_blockers=4
```

The C++ and Python pair-blocker histograms agree exactly:

| Pair blockers | Couplings |
|---:|---:|
| 4 | 22485 |
| 5 | 38832 |
| 6 | 23313 |
| 7 | 5614 |
| 8 | 634 |
| 9 | 20 |

## Evidence

The finite outputs are `COMPUTED`. The mathematical exclusions are
`PROVED_CANDIDATE` only after combining them with the arbitrary-finite
reductions in the proof. No solver, floating-point arithmetic, randomness,
or network access is used. All middle splits are excluded, giving the
candidate conclusion $\operatorname{sat}(7)=55$ relative to the frozen
inputs. Isolated-Referee acceptance remains pending.
