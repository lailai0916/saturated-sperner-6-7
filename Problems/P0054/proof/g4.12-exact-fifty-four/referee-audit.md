# P0054 G4.12 isolated Referee report

```text
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
REVIEWED_HEAD: 58f005e2f0bde9103acd15d37a6a22ce16308ad9
FROZEN_SUBPROBLEM_SHA256: d3dc887cc95136d5eeecc58ddf09f8cd589d49486867a55fa7b1c20f57248957
CANDIDATE_SHA256: 34523d981c6f32e03dff873bc488c7b3832341db9459716a1d7058db495ed1ce
MANIFEST_SHA256: af0093442958622c7b6a7fb52201da6fb153ce4725c2d922aadedcc2a0f85bbd
NETWORK_USED: NO
WORKTREE_MODIFIED_BY_REFEREE: NO
```

## 1. Repair history

The first reviewed candidate had SHA-256
`b08f4beb8348fa67b9b9fe65743a0c5b16a591b34d3bc470705dca29209a03fe`.
The Referee rejected its exclusion of the $(6,10)$ middle split. Sections 8
and 9 covered the cases in which some point has degree three and in which
every point has degree at most two, but no preceding lemma excluded a point
of degree four on the six-row side.

The accepted repair is the candidate bound by the final hash above. It adds
Lemma 8.1 and does not change any finite enumerator or saved output.

## 2. Lemma 8.1 audit

`PROVED`: the repaired degree reduction is dependency-closed.

- Degrees six and five give a transversal of size at most two, contradicting
  the minimum row size three in the blocker family.
- At degree four, let $P,Q$ be the two rows avoiding the chosen point $x$.
  They are disjoint, since otherwise $x$ and a common point form a two-point
  transversal.
- For every $(p,q)\in P\times Q$, the set $\{x,p,q\}$ is a minimal blocker.
  The rows $P,Q$ are private for $p,q$. If no row were private for $x$, then
  $\{p,q\}$ would be a two-point transversal.
- Since $|P|,|Q|\ge3$, there are at least nine blockers containing $x$.
  The residual clutter after deleting $x$ has row-size minimum two, so the
  frozen residual lemma supplies at least two blockers avoiding $x$.
- Thus the ten-row blocker family would contain at least eleven rows, a
  contradiction.

Every point on the six-row side therefore has degree at most three. The cases
"some point has degree three" and "every point has degree at most two" are
now exhaustive.

## 3. Mathematical verdict

The Referee audited the repaired candidate proof and its arbitrary-finite
reductions.

- The frozen slack reduction leaves only the Fano profile
  $(1,6,13,14,13,6,1)$ and the sixteen-middle profile
  $(1,6,12,16,12,6,1)$.
- The Fano adjacent splits $(7,6)$, $(8,5)$, and $(9,4)$, and their exact
  duals, are impossible.
- Every sixteen-member middle blocker pair has a three-point row.
- The middle splits $(5,11)$, $(6,10)$, $(7,9)$, and $(8,8)$, and their
  blocker duals, are impossible.
- The finite reductions retain inactive points, parallel actual points,
  repeated incidence patterns, nonuniform rows, and arbitrary finite ground
  sets.

No fifty-four-member profile survives. Combined with the frozen lower bound
and the frozen 55-member construction, the accepted candidate establishes

```text
PROVED_CANDIDATE: sat(7) = 55
```

## 4. Computation and source audit

The candidate manifest binds 36 frozen, proof, source, output, and report
objects. All 36 hashes matched. The 18 frozen input hashes also matched.

The Referee independently replayed the three C++ and three Python outputs used
in the $(7,9)$ exclusion. The outputs were byte-identical to the saved
evidence, including:

```text
four-row kernel classes:                 11
extension candidates:                138161
valid extensions:                         0
five-row classes with minimum row four:   0
six-row minimum pair blockers:             4
```

The Referee also audited the four-row arbitrary-finite reduction, the
five-row private-row argument, the six-row marginal coupling, and the final
blocker injections. The amended pair-minimality argument is sound.

These exhaustive results retain the label `COMPUTED`. They become proof
dependencies only through the proved arbitrary-finite reductions.

## 5. Evidence boundary

`UNKNOWN`: novelty, priority, and a Lean formalization of the exact-value
candidate.

No change to `claims.yaml` or `status.md`, publication, expert contact, push,
authorship change, or next gate is included. The Referee used no network and
modified no repository file.
