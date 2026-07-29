# P0054 G4.11 kernel experiment report

```text
GATE: P0054_G4_11_COUPLED_TOTAL_FIFTY_THREE
LABEL: COMPUTED
NETWORK: MATHEMATICS_OFFLINE
GLOBAL_LOWER_BOUND_FROM_COMPUTATION_ALONE: NO
```

## Scope

The saved programs implement the two arbitrary-finite kernel reductions in
the G4.11 candidate. They preserve actual parallel points through incidence
support multiplicities. The programs do not search a fixed ground-set size.

The four-row checker covers a kernel obtained when a three-point blocker lies
on the eight-row middle side. The five-row checker and extension cover the
opposite orientation. The Python verifier independently checks every saved
representative and extension candidate with choice-union blocker
minimalization.

## Toolchain

```text
Apple clang version 21.0.0 (clang-2100.1.1.101)
Python 3.12.13
```

All commands ran from the execution checkout with network access unused.

## Replay commands

```text
clang++ -std=c++17 -O3 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.11-coupled-fifty-three/four-row-kernel.cpp \
  -o /tmp/g411-four-row-kernel
/tmp/g411-four-row-kernel \
  > Problems/P0054/experiments/g4.11-coupled-fifty-three/four-row-kernel-results.txt

clang++ -std=c++17 -O3 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.11-coupled-fifty-three/five-row-kernel.cpp \
  -o /tmp/g411-five-row-kernel
/tmp/g411-five-row-kernel \
  > Problems/P0054/experiments/g4.11-coupled-fifty-three/five-row-kernel-results.txt

clang++ -std=c++17 -O3 -Wall -Wextra -Werror -pedantic \
  Problems/P0054/experiments/g4.11-coupled-fifty-three/five-row-extension.cpp \
  -o /tmp/g411-five-row-extension
/tmp/g411-five-row-extension \
  Problems/P0054/experiments/g4.11-coupled-fifty-three/five-row-kernel-results.txt \
  > Problems/P0054/experiments/g4.11-coupled-fifty-three/five-row-extension-results.txt

UV_OFFLINE=1 uv run --offline python \
  Problems/P0054/experiments/g4.11-coupled-fifty-three/verify.py \
  --four-row-results \
  Problems/P0054/experiments/g4.11-coupled-fifty-three/four-row-kernel-results.txt \
  --five-row-results \
  Problems/P0054/experiments/g4.11-coupled-fifty-three/five-row-kernel-results.txt \
  > Problems/P0054/experiments/g4.11-coupled-fifty-three/verification.json
```

The three C++ programs were also compiled with AddressSanitizer and
UndefinedBehaviorSanitizer at `-O0`. Their outputs were byte-identical to the
saved optimized outputs. Ruff and mypy accepted `verify.py`.

## Four-row output

`COMPUTED`: the checker exhausted 14 nonempty rank-at-most-three supports and
all 16,383 nonempty active support masks. It retained 910 support-feasible
masks and one actual multiplicity vector:

```text
supports=14
minimal_support_covers=48
active_masks_checked=16383
support_feasible_masks=910
multiplicity_vectors=1
blockers=7 pairs=3 vectors=1
canonical_classes=1
class=3:1,5:1,6:1,9:1,10:1,12:1,|b:7|p:3
```

The unique class is the six-edge incidence clutter of $K_4$.

## Five-row output

`COMPUTED`: the checker exhausted 25 nonempty rank-at-most-three supports and
all 33,554,431 nonempty active support masks. The complete output is:

```text
supports=25
minimal_support_covers=396
active_masks_checked=33554431
support_feasible_masks=55023
multiplicity_vectors=490
blockers=6 pairs=3 vectors=20
blockers=7 pairs=3 vectors=470
canonical_classes=8
```

There is one six-blocker class and seven seven-blocker classes. The extension
program reads these classes from the saved output rather than embedding them.

## Extension output

`COMPUTED`: seven classes have a determined seven-row blocker side. The one
six-blocker class has 48 admissible choices for its remaining row, including
every allowed number of fresh parallel points private to that row. The output
is:

```text
total_q_candidates=55
total_valid_extensions=0
```

For every candidate, the program recomputes the blocker on the expanded
actual point set. It requires eight rows, retains the original five kernel
rows, enforces both row-size ranges, enforces point degree at most three on
both sides, and requires exactly three rows containing the distinguished
point.

## Independent verification

`COMPUTED`: `verify.py` reconstructs the saved incidence classes and computes
blockers by iterative choice-union minimalization. It independently returns:

```text
four-row classes:                 1
five-row classes:                 8
five-row Q candidates:           55
valid extensions:                 0
three-row labelled solutions:     3
```

The three labelled integer solutions are one orbit of
$(p,q,r;x,y,z)=(1,2,2;1,1,0)$.

## Hashes

```text
four-row-kernel.cpp
  90beba15e882f076daf18facf49a5cd5051474f3692d636b648db6de89062dc5
four-row-kernel-results.txt
  21849a7032e719bd195ecf893ccb6d3307077fbb031b6965d3ee07b3f5914c23
five-row-kernel.cpp
  1f11efbb7c018ee726bb327d3ce29088e68754a02534c3819ea1d6d3ef85fbd2
five-row-kernel-results.txt
  9069cbceab1612fd1268c8d28e5a0fe9d4b94d3f5f9067729cbbcc01fafcfd38
five-row-extension.cpp
  87fe0c2993363281de81850808f2ec5e9f17cfd8e46de0d80105880f65347bed
five-row-extension-results.txt
  ad1e8a68e39206ae653ebe6925b3b8dff00e9e0e1c1e62a38892086e14868ab6
verify.py
  26d637633cd373ff1f1602a9e4f83e77960f8255898dfd6d8417c9989781c7c5
verification.json
  59838a02d3c1a7fa402019f82ba75798d1d1dc03147c1069d1f53ee2fceaa78d
```

## Evidence boundary

The finite outputs are `COMPUTED`. They become proof dependencies only after
the candidate's arbitrary-finite reductions and an independent source and
output audit. They do not alone prove a global lower bound, exact
$\operatorname{sat}(7)$, novelty, or priority.
