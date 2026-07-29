# P0054 G4.11 isolated Referee report

```text
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
REVIEWED_HEAD: bb73a8524d79621ca1aa185b82426bd4f39d5b21
FROZEN_SUBPROBLEM_SHA256: 37c422adc330ceb43ffca7b930f3da0b7c46ee5ece3d0c1da2e7186695eeca34
CANDIDATE_SHA256: 74c790f92d68728fd858aed64f3222700793db5f00a9f683c8f1699f8498b553
NETWORK_USED: NO
WORKTREE_MODIFIED_BY_REFEREE: NO
```

## 1. Repair history

The first reviewed candidate had SHA-256
`5399f61187c05773e4bb35f01e5214916d3669573c1c87dd4bf2159c3cf0bd23`.
The Referee rejected Lemma 4.2 because it attributed a 15-blocker lower bound
to every degree-at-most-two six-row clutter. The frozen G4.10 enumeration only
covers inclusion-minimal cores with an actual perfect matching.

The first repair had SHA-256
`c4102d9c404d75244d9fb5a16115897b62070022b9d80ff8643a0f915653ff16`.
It supplied the missing matching-number-two argument, but still applied the
perfect-matching enumeration to the original support. A perfect matching in
the original support need not survive in an inclusion-minimal degree-three
core, so the Referee rejected this version as well.

The accepted repair first chooses an inclusion-minimal submultigraph $J$ with
minimum row degree three and classifies the matching number of $J$. This is
the reviewed candidate bound by the final hash above.

## 2. Lemma 4.2 audit

`PROVED`: the repaired low-degree argument is dependency-closed.

- Finiteness guarantees an inclusion-minimal core $J$.
- Every minimal edge cover of $J$ has a private row for each selected actual
  point. It is therefore a minimal blocker of the original clutter
  $\mathcal D$.
- If $\nu(J)=0$ or $1$, the frozen G4.8 choice injections give at least
  $3^6$ or $3^4$ blockers.
- If $\nu(J)=2$, fix an actual two-edge matching with unmatched vertices
  $u,v$. The frozen construction gives $d(u)d(v)\ge9$ blockers inside
  $S=I(u)\cup I(v)\cup M$.
- When $d(u)=d(v)=3$, the four matched vertices require at least 12 row
  incidences. The two matching points and the six points incident with $u$ or
  $v$ contribute at most ten. Hence some point $z$ of $J$ lies outside $S$.
- Every active point of a finite clutter belongs to a minimal blocker. A
  blocker containing $z$ is distinct from the first nine blockers inside
  $S$, so this branch has at least ten.
- If $\nu(J)=3$, inclusion-minimality makes every actual point of $J$ touch a
  degree-three vertex. Together with the actual perfect matching, this places
  $J$ exactly in the frozen G4.10 enumeration domain. The enumeration gives
  at least 15 minimal edge covers.

Thus every degree-at-most-two case contradicts
$|B(\mathcal D)|=9$. The remaining degree-three reduction is valid.

## 3. Mathematical verdict

The Referee audited the candidate proof and its arbitrary-finite reductions.

- The total-53 slack reduction leaves only the profile
  $(1,6,12,15,12,6,1)$.
- The upper compressed interface is equivalent to the frozen ordered
  predecessor and successor conditions.
- The splits $(5,10)$, $(10,5)$, $(6,9)$, and $(9,6)$ are impossible.
- The point-degree reductions for $(7,8)$ and $(8,7)$ preserve loops,
  parallel actual points, repeated incidence patterns, and nonuniform row
  sizes.
- The four-row kernel has the unique $K_4$ edge-clutter class.
- The five-row kernel has 490 multiplicity vectors in eight row-permutation
  classes. All 55 extensions fail the required blocker and degree checks.

The total-fifteen middle blocker pair is therefore impossible. Relative to
the frozen eventual-stability reduction, the accepted candidate establishes

```text
PROVED_CANDIDATE: sat(7) >= 54
```

## 4. Computation and source audit

The manifest binds 23 candidate, input, source, output, report, and frozen
statement objects. All 23 hashes matched.

The Referee compiled all three C++ programs with strict warnings and replayed
the saved outputs byte-for-byte. The independent Python verifier reproduced:

```text
four-row classes:                 1
five-row multiplicity vectors: 490
five-row classes:                 8
five-row Q candidates:           55
valid extensions:                 0
```

These exhaustive results retain the label `COMPUTED`. They become proof
dependencies only after the proved arbitrary-finite reductions. They do not
independently establish a global lower bound.

## 5. Evidence boundary

`UNKNOWN`: exact $\operatorname{sat}(7)$, novelty, priority, and Lean
formalization of the candidate lower bound.

No change to `claims.yaml` or `status.md`, publication, expert contact, push,
or G4.12 work is included. The Referee used no network and modified no
repository file.
