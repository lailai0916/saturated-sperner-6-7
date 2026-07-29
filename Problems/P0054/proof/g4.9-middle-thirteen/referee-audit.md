# P0054 G4.9 isolated Referee report

```text
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
REVIEWED_COMMIT: 6c88f28da99f9d6b831a441a46f73f05eff3bc0e
CANDIDATE_SHA256: c62752dfc9cdcd4a078f4b1568cd0b1ab046bc4d786a987516cf45e3940f25e1
NETWORK_USED: NO
WORKTREE_MODIFIED_BY_REFEREE: NO
REQUIRED_CORRECTION: NONE
```

All five frozen-input hashes match `frozen-subproblem.md`.

## Dependency audit

`PROVED`: G4.8 is used only for its proved three-row bound, prior branch
bounds, split classification, middle-layer interface, and frozen layer
reduction. The G4.6 computation is not used as proof.

## Mathematical verdict

`PROVED`: the candidate establishes, for arbitrary finite ground sets,

$$
m(3,3)\ge14
$$

and therefore, relative to the frozen layer interface,

$$
\operatorname{sat}(7)\ge52
$$

The three total-thirteen splits are independently closed:

- `(4,9)`: the four-row intersection graph is covered by the isolated-component
  cases and the three-leaf star. The exact star count gives at least $19$
  blockers.
- `(5,8)`: blocker involution forces at least four residual blockers avoiding
  the shared matching point. The formerly tight branch therefore has at least
  nine blockers.
- `(6,7)`: the degree-three equality case has an eighth blocker outside the
  G4.8 injection. The perfect-matching residual count gives at least seven
  members of the double blocker, contradicting the six original rows.

## Critical audits

Lemma 2.1 exhausts every minimal transversal of a three-row clutter. Its four
multiplicity cases correctly force at least nine blockers when $pqr\ge2$.

Lemma 2.2 correctly applies blocker involution to zero or one arbitrary added
row and to two added rows of size at least two.

In the six-row degree-three branch, the G4.8 injection gives seven blockers.
Lemma 2.1 permits at most one image blocker avoiding $x$. The residual clutter
has at least two blockers avoiding $x$, so one lies outside the image.

In the six-row perfect-matching branch, $D$ has at least four rows. For every
$Q\in B(L_e)$, the set $\{e\}\cup Q$ is minimal: $M$ is private for $e$, and
each point of $Q$ retains a private row in $D$ or an uncovered $N_j$. Different
$e$ give disjoint families. The cases $s\le1$, $|I_1\cup I_2|\ge2$, and the
common singleton produce at least $9$, $7$, and $7$ rows of $B(C)$,
respectively. Each contradicts $|H|=6$.

## Boundary audit

- Inactive points cannot occur in minimal transversals.
- Actual-point counting retains loops and parallel points.
- Inclusion minimization handles repeated residual supports.
- Empty incidence classes and nonuniform row sizes are covered.
- The proof is finite and set-theoretic and remains valid after exchanging the
  two blocker orientations.
- No computational result is promoted to proof.
- Exact $m(3,3)$, exact $\operatorname{sat}(7)$, novelty, and priority remain
  `UNKNOWN` under this gate.
- Promotion to `claims.yaml` or `status.md` remains outside this gate.
