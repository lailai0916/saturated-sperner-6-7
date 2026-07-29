# Computational audit for $m(2,3)$

```text
EPISTEMIC_LABEL: COMPUTED
ROLE: REGRESSION_AND_COUNTEREXAMPLE_SEARCH
PROOF_DEPENDENCY: NO
NETWORK: OFFLINE
```

## Scope

The search checks mutual-blocker pairs $(\mathcal S,\mathcal C)$ satisfying

$$
|S|\ge2,\qquad |C|\ge3
$$

for every member. It exhausts all ordered cardinality splits with

$$
|\mathcal S|\ge3,\qquad |\mathcal C|\ge2,
\qquad 5\le|\mathcal S|+|\mathcal C|\le9
$$

The lower cardinality bounds follow from the private-witness injection.

## Coverage reduction

The primary clutter has $r$ labelled rows. Every active ground point is
represented by its nonzero incidence pattern in $\{1,\dots,2^r-1\}$. Equal
patterns retain exact positive integer multiplicities.

The private-witness injection bounds every primary row size by the number of
members in its blocker. Therefore every pattern multiplicity is bounded.
Deleting inactive ground points loses no minimal transversal. The search is
thus exhaustive for arbitrary finite ground sets, subject to the stated
family cardinalities and member-size conditions.

The engine quotients row permutations and counts minimal pattern covers with
exact integer weights. It uses no randomness and no floating-point
arithmetic.

## Independent semantic checks

Two blocker implementations were compared:

1. full powerset enumeration followed by inclusion minimization;
2. one-point-per-row choice unions followed by inclusion minimization.

They agree on all 199 clutters on ground sets of size at most four. Both
implementations satisfy blocker involution in these tests. The direct and
incremental incidence-cover engines agree in 194 nonempty cases.

The explicit six-point witness was checked in both blocker directions:

$$
\mathcal S=
\{\{0,2\},\{0,3\},\{1,2\},\{1,3\},\{4,5\}\}
$$

$$
\mathcal C=
\{\{0,1,4\},\{0,1,5\},\{2,3,4\},\{2,3,5\}\}
$$

Both validators confirm $\mathcal S=B(\mathcal C)$ and
$\mathcal C=B(\mathcal S)$.

## Results

Every one of the 10 ordered splits of total at most eight returned
`UNSAT_COMPUTED` with complete exhaustion. The total-nine search returned
`SAT_COMPUTED` for $(a,b)=(5,4)$ and verified its first witness. The other
four total-nine splits returned `UNSAT_COMPUTED`.

The search visited 16738 depth-first nodes for totals at most eight and
182949 nodes across all totals. No case reached its deadline.

## Reproduction

```bash
UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run --offline python \
  Problems/P0054/experiments/sat6-exact/search.py \
  > Problems/P0054/experiments/sat6-exact/results.json

UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run --offline python \
  Problems/P0054/experiments/sat6-exact/search.py \
  --verify-results Problems/P0054/experiments/sat6-exact/results.json \
  > /tmp/p0054-sat6-replay.json
```

The stable replay matched the saved result after excluding wall-clock timing.

| Artifact | SHA-256 |
|---|---|
| `search.py` | `c413440e70f6e5073a6d63e0e1e3d77716d9d268457da3601187cec9ed2a0eda` |
| `results.json` | `70442058abd96e6b6d5836f52fe9212de3b534c54500aef277ea9642c47f5145` |
| reused G4.4 engine | `50a1016029f1b57138a9209adbe6cd1d22a1a759cc802a9df3e6dc3ebf78fe58` |

`COMPUTED`: these results corroborate $m(2,3)=9$. The arbitrary-finite-set
proof is recorded separately and does not invoke this enumeration.
