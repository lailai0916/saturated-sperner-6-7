# P0054 G4 gap list

```text
UPDATED_FOR: DEPENDENCY_RESOLVED_37_PROOF_AFTER_TWO_REFEREE_ACCEPTS
OPEN_CRITICAL_MATHEMATICAL_GAPS: 0
GATE_ACCEPTANCE: REFEREE_A_ACCEPT; REFEREE_B_ACCEPT
```

## Closed or corrected items

| ID | Exact issue | Resolution | Status |
|---|---|---|---|
| G4-G01 | Can the stable ground set be chosen large enough for the atom theorem without using the candidate lower bound? | Use existing `sat(7)<=55`, then choose stable `n>2^55`. | `PROVED` |
| G4-G02 | Does endpoint normalization preserve minimum cardinality? | Gerbner et al. Lemma 6 is an existential replacement at no size increase; starting from a minimum keeps equality. | `PROVED` from `LITERATURE` |
| G4-G03 | Are there exactly seven nonempty canonical layers? | Saturation of an omitted set gives a seven-chain in `F`; 7-Sperner forbids height eight; canonical ranks are `0,...,6`. | `PROVED` |
| G4-G04 | Is the same `H` a maximal homogeneous atom of every layer? | No. Endpoint singleton layers have maximal atom `X`, while the family atom `H` is proper. Replace this with one inherited all-or-none block plus separate layer saturation. | `REFUTED` literal wording; dependency repaired |
| G4-G05 | Are the endpoint layers singletons? | Endpoint normalization and the canonical rank/antichain argument give `A_0={empty}`, `A_6={X}`. | `PROVED` |
| G4-G06 | Are `|A_1|,|A_5|>=6` available with the selected-family hypotheses? | Martin--Veldt Lemma 15 supplies these bounds at `k=7`; source hypotheses are restated in the candidate proof. | `PROVED` from `LITERATURE` |
| G4-G07 | Does layer saturation give the required orientation for each core set `R`? | Test `R union Q` for a nonempty proper `Q subset H`; homogeneity excludes it from `F` and forces the orientation. | `PROVED` |
| G4-G08 | Can exact rational counting give `|A_2|,|A_4|>=7`? | At `p=2/5,3/5`, every event is capped by `4/25`; six events total at most `24/25`. | `PROVED` |
| G4-G09 | Does the middle estimate stop at eight? | Equality forces event weight `1/8` and pointwise multiplicity one; `R=empty,U` force one large and one small member, contradicting eight. | `PROVED` |
| G4-G10 | Is the final statement global rather than template-restricted? | Every stable minimum family may first be endpoint-normalized and, after choosing `n>2^55`, receives the needed atom; no extra family-class assumption is imposed. | `PROVED` |
| G4-G11 | Does the actual VOR require `|H|>2`? | No; it uses `|H|>=2`, which is also sufficient for the proof. Older local transcription is retained only as a source-text mismatch. | `LITERATURE` mismatch resolved |

## Referee gate results

| ID | Exact issue | Consequence if failed | Current status |
|---|---|---|---|
| G4-O01 | Referee A must reconstruct the stable-`n`, minimum-family, canonical-decomposition, and source-hypothesis chain. | No C17 if failed. | `ACCEPT` |
| G4-O02 | Referee B must independently attack the oriented cover, exact weights, and middle equality exclusion. | No C17 if failed. | `ACCEPT` |
| G4-O03 | The prior-art classification must account for the printed Martin--Veldt Lemma 17 specialization and its central strictness boundary. | No novelty/priority wording; classify 37 as a published-statement specialization with an independently repaired equality seam unless stronger source evidence is found in a future gate. | `UNKNOWN` bibliographic interpretation; no effect on proof validity |

## Computation-only residuals

- `COMPUTED`: the bounded SMT audit returned `UNSAT` for middle-layer size at
  most eight for core sizes through six, but timed out at core size seven.
  This timeout is not a dependency of the global proof.
- `COMPUTED`: exact event identities and same-side intersections were replayed
  on finite cores through the recorded limits. They corroborate but do not
  replace the proof.
- `UNKNOWN`: no stronger global bound than 37 has been investigated in G4.

## Prohibited extrapolations

- `REFUTED`: a class-restricted G0--G3 certificate is not a global lower
  bound.
- `UNKNOWN`: the exact value of `sat(7)` remains unknown.
- `UNKNOWN`: novelty, priority, and worldwide absence are not established.
- `DEFINITION`: Formalization belongs to a separately authorized G5; it is
  prohibited in this gate.
