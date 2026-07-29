# P0054 G4.8 discarded five-cycle lift

```text
STATUS: REFUTED_CANDIDATE_CONSTRUCTION
TARGET_SPLIT: (6,6)
FIRST_INVALID_STEP: assuming the five old cycle blockers are the only blockers avoiding or mixing the added matching points
```

## Construction tested

On ground points `0,...,7`, consider the six-row clutter

```text
{0,1,5}, {1,2,5}, {2,3,6},
{3,4,6}, {4,0,7}, {0,1,7}.
```

The first five residual pairs form a five-cycle, the sixth repeats one cycle
edge, and `5,6,7` form a perfect matching across the six rows. Every row has
size three, and the matching is a three-point transversal.

## Refutation

`COMPUTED`: both the direct powerset blocker and independent choice-union
minimization validator return the same blocker with fifteen members, fourteen
of size three and one of size four. Applying both validators again returns the
original six-row clutter.

The five old minimum vertex covers and the added matching are not the complete
blocker. Nine additional mixed transversals appear. Therefore this construction
does not realize a `(6,6)` mutual-blocker pair and supplies no upper bound on
`m(3,3)`.
