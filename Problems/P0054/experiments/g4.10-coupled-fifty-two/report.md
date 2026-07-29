# P0054 G4.10 exact enumeration report

```text
LABEL: COMPUTED
GATE: P0054_G4_10_COUPLED_TOTAL_FIFTY_TWO
BASE_HEAD: 5b35bda08342279db986dca5971434182ee9d2b7
NETWORK: MATHEMATICS_OFFLINE
```

## Scope

The computation has three proof-facing components:

1. exact loop-multigraph support kernels for the asymmetric splits $(5,9)$
   and $(6,8)$;
2. complete four-row kernel enumeration for the $(7,7)$ reduction;
3. complete seven-row extension of all 41 kernel classes, requiring a
   three-point blocker but not a three-point primary row.

The arbitrary-finite reductions are mathematical arguments in
`candidate-proof.md`. These programs do not establish those reductions by
themselves.

## Environment

```text
OS: macOS 27.0 build 26A5388g, arm64
Python: 3.12.13
uv: 0.11.29
C++: Apple clang 21.0.0
```

## Commands

```bash
uv run python Problems/P0054/experiments/g4.10-coupled-fifty-two/support-multigraph-checker.py \
  --output Problems/P0054/experiments/g4.10-coupled-fifty-two/support-multigraph-results.json

clang++ -std=c++17 -O2 -Wall -Wextra -pedantic \
  Problems/P0054/experiments/g4.10-coupled-fifty-two/four-row-kernel.cpp \
  -o /tmp/p0054-g410-four-row-kernel

/tmp/p0054-g410-four-row-kernel \
  Problems/P0054/experiments/g4.10-coupled-fifty-two/four-row-kernel-results.txt

clang++ -std=c++17 -O2 -Wall -Wextra -pedantic \
  Problems/P0054/experiments/g4.10-coupled-fifty-two/seven-row-extension.cpp \
  -o /tmp/p0054-g410-seven-row-extension

/tmp/p0054-g410-seven-row-extension \
  Problems/P0054/experiments/g4.10-coupled-fifty-two/four-row-kernel-results.txt \
  Problems/P0054/experiments/g4.10-coupled-fifty-two/seven-row-extension-results.txt
```

## Results

`COMPUTED`: the asymmetric support checker reproduced:

| Split | Low-degree count | Vectors | Minimum blockers |
|---|---:|---:|---:|
| $(5,9)$ | 3 | 54 | 19 |
| $(5,9)$ | 4 | 2445 | 16 |
| $(5,9)$ | 5 | 2698 | 15 |
| $(6,8)$ | 4 | 2601 | 24 |
| $(6,8)$ | 5 | 31772 | 21 |
| $(6,8)$ | 6 | 27325 | 15 |

`COMPUTED`: the four-row checker reproduced:

```text
degree_feasible_vectors=7063970
valid_clutters=6049557
blocker_count=5 vectors=6
blocker_count=6 vectors=89
blocker_count=7 vectors=475
low_isomorphism_classes=9
equality_isomorphism_classes=32
```

The report has 41 unique full keys and 41 unique base multiplicity keys.

`COMPUTED`: the seven-row checker reads those keys directly and reproduced:

```text
kernels=41
class_nodes=213692
new_point_nodes=8178773
blocker_prunes=8858786
valid_vectors=6
non_fano_vectors=0
```

Unlike the superseded exploratory source, the saved extension checker does
not require a primary row of size three. It only requires the three-point
blocker supplied by the random-subset lemma in the candidate proof. It also
allows blockers of size one or two, so its search class is larger than the
candidate theorem's class.

## Independent replay

`COMPUTED`: a read-only audit compiled both C++ sources with
`-O3 -Wall -Wextra -Werror -pedantic`, regenerated the four-row report, and
ran the extension against both the regenerated and saved reports. The two
extension outputs were byte-identical. It separately reran the Python checker
and obtained a byte-identical JSON output.

That audit initially used Python source hash
`e38288bdfb25a57c0230ab19efd5c8867accb123ba99586d2004c274bafca6b9`.
A later safety-only edit added `strict=True` to `zip`, producing the final
source hash `4dd7168574b9f1e2e0332a4851e46ec2f1215af183de0513aa800373cf025587`
recorded below. The final source was replayed independently twice and again
produced the saved JSON byte-for-byte.

The audit returned:

```text
FIRST_INVALID_STEP=NONE
```

This is an implementation audit, not the isolated mathematical Referee for
the complete candidate.

## Hashes

```text
c82b485af00399be79f36be46d8b6cece90dd4828a9a065d148305ea71410db4  frozen-subproblem.md
5525e73d5d25394f2e35bcf051968243fb70597e63daa43e9fc0e773b853d454  candidate-proof.md
4dd7168574b9f1e2e0332a4851e46ec2f1215af183de0513aa800373cf025587  support-multigraph-checker.py
bd58fded081a9f704187c4ab972d3be955b268c0f9d8d14f02388c8a4b4fb590  support-multigraph-results.json
fc4f1504838010e86f661edce849dbf7ae3f42681820bca96d1ff0c66b9daec7  four-row-kernel.cpp
5cad55dc857e02fadb586c671de68e52903d201c6cb654b54694376fd146bfde  four-row-kernel-results.txt
8004d3d39212c1b0ece8255f010553445516317820c880234dbe7173a2bcdf5d  seven-row-extension.cpp
f222ac792ca96642cc53c0c1b2d6ae58819e2230e665e8b4945ffcf1699cf26f  seven-row-extension-results.txt
```

## Boundary

The outputs are exact finite certificates attached to proved finite
reductions. They do not independently prove a global bound. No claim, status,
publication, push, or G4.11 action is authorized by this report.
