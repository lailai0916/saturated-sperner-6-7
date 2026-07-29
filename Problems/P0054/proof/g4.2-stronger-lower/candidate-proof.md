# P0054 G4.2 dependency-resolved candidate proof

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_2_INTERNAL_LAYER_EQUALITY_CLASSIFICATION
CANDIDATE_THEOREM: sat(7) >= 39
CANDIDATE_STATUS: DEPENDENCY_RESOLVED_PENDING_TWO_REFEREES
NETWORK: OFFLINE; NOT_USED
FORMALIZER: FORBIDDEN; NOT_USED
PUBLICATION_COMMIT_PUSH: FORBIDDEN; NOT_USED
```

## 1. Exact statement and evidence boundary

`PROVED` relative to the frozen G4 proof and the deductions below: every
second internal layer in the G4 global minimum-family setting satisfies

\[
|A_2|\ge 8.
\]

`PROVED`: complementing the core variable and exchanging the two oriented
sides gives the dual bound `|A_4|>=8`. Together with the frozen G4 layer
bounds this yields the candidate global theorem

\[
\operatorname{sat}(7)\ge39.
\]

`DEFINITION`: the word `PROVED` in this candidate records a dependency-
resolved deduction awaiting the two required isolated Referees. P0054-C18
may be created only after both Referees return `ACCEPT`.

`DEFINITION`: finite SMT results in the Experimentalist report are only
`COMPUTED`; they are not dependencies of this proof.

## 2. Frozen G4 global framework

`PROVED` (frozen P0054-C17 proof): choose a ground set in the eventual stable
range with size greater than `2^55`, and choose an endpoint-normal minimum
saturated 7-Sperner family `F`. P0054-C7 gives `|F|<=55`, so the frozen
homogeneous-atom theorem supplies an all-or-none block `H` with `|H|>=2`.
The canonical decomposition has exactly seven nonempty saturated-antichain
layers

\[
F=A_0\mathbin{\dot\cup}\cdots\mathbin{\dot\cup}A_6.
\]

Put `U=X\H`. The accepted frozen bounds are

```text
|A0|=1, |A1|>=6, |A2|>=7, |A3|>=9,
|A4|>=7, |A5|>=6, |A6|=1.
```

`PROVED` (frozen local interface): for an internal layer `A_i`, call a member
small when it is disjoint from `H`, and write a large member as `K union H`
with trace `K subseteq U`. Then

\[
|S|\ge i\quad\hbox{for small }S,
\qquad
|U\setminus K|\ge6-i\quad\hbox{for large traces }K.       \tag{1}
\]

For every `R subseteq U`, oriented layer saturation gives

\[
\sum_{S\text{ small}}1[S\subseteq R]
+\sum_{K\text{ large trace}}1[R\subseteq K]\ge1.          \tag{2}
\]

Every layer is an antichain. Hence the small traces form an antichain, the
large traces form an antichain, and for every small `S` and large trace `K`,

\[
S\nsubseteq K.                                             \tag{3}
\]

No G0--G3 fixed-core certificate is used below.

## 3. Exact Bernoulli count classification for a seven-member `A_2`

Assume for contradiction that `|A_2|=7`. Let `a` be the number of small
members and `b` the number of large members, so `a+b=7`. For a large trace
`K_j`, put `C_j=U\setminus K_j`. By (1),

\[
|S_i|\ge2,\qquad |C_j|\ge4.                               \tag{4}
\]

`PROVED`: for every rational `0<p<1`,

\[
1\le a p^2+b(1-p)^4.                                      \tag{5}
\]

Indeed, include each point of finite `U` independently with probability
`p`. Taking expectations in (2) gives

\[
1\le\sum_i p^{|S_i|}+\sum_j(1-p)^{|C_j|}
 \le a p^2+b(1-p)^4.
\]

All comparisons are exact rational comparisons. Event overlaps are allowed;
only linearity of expectation is used.

`PROVED`: the eight nonnegative integer splits of `a+b=7` have the following
exact classification.

| `(a,b)` | rational witness or surviving check | status |
|---|---|---|
| `(0,7)` | `p=1/2`: `7/16<1` | `REFUTED` |
| `(1,6)` | `p=1/2`: `10/16<1` | `REFUTED` |
| `(2,5)` | `p=1/2`: `13/16<1` | `REFUTED` |
| `(3,4)` | `p=2/5`: `624/625<1` | `REFUTED` |
| `(4,3)` | inequality (6) below holds for every `0<p<1` | only survivor |
| `(5,2)` | `p=1/3`: `77/81<1` | `REFUTED` |
| `(6,1)` | `p=1/3`: `70/81<1` | `REFUTED` |
| `(7,0)` | `p=1/3`: `63/81<1` | `REFUTED` |

`PROVED`: `(4,3)` really survives every count-only Bernoulli inequality. Put
`q=1-p` and `r=5/8`. The exact identity

\[
q^4-4r^3q+3r^4=(q-r)^2((q+r)^2+2r^2)\ge0
\]

gives, after completing the square,

\[
4p^2+3(1-p)^4
\ge1+4\left(p-\frac{375}{1024}\right)^2
       +\frac{5231}{262144}>1.                            \tag{6}
\]

Thus the probability classification has exactly one surviving split:

\[
(a,b)=(4,3).                                               \tag{7}
\]

Larger actual generator or complement sizes only reduce the exact event
probabilities, so they cannot repair any split already refuted by (5).
Survival of (7) is only a necessary count condition, not existence.

## 4. Blocker recognition

`DEFINITION`: a transversal of a finite set family meets every member. Its
blocker `B(G)` is the family of inclusion-minimal transversals.

`PROVED` (recognition lemma): let `G` be an antichain. If every member of `G`
is a transversal of `J`, and every transversal of `J` contains a member of
`G`, then `G=B(J)`.

Proof. If a proper subset of a member `G_0` were a transversal, the
containment hypothesis would put another member of the antichain strictly
below `G_0`. Thus every `G_0` is minimal. Conversely, a minimal transversal
contains some `G_0`, and its minimality forces equality. `QED`

For the surviving split, write

\[
\mathcal S=\{S_1,S_2,S_3,S_4\},\qquad
\mathcal C=\{C_1,C_2,C_3\}.
\]

`PROVED`: every `S_i` meets every `C_j`. Equation (3) says
`S_i` is not contained in `K_j=U\setminus C_j`, which is equivalent to
`S_i intersect C_j` being nonempty.

`PROVED`: `\mathcal S=B(\mathcal C)`. Each `S_i` is a transversal by the
previous paragraph. If `R` is any transversal of `\mathcal C`, then `R` is
not contained in any `K_j`; equation (2) therefore forces some `S_i subseteq
R`. The small family is an antichain, so the recognition lemma applies.

`PROVED`: `\mathcal C=B(\mathcal S)`. Each `C_j` is a transversal of
`\mathcal S`. If `D` is any transversal of `\mathcal S`, apply (2) to
`R=U\setminus D`. No `S_i` is contained in `R`, so (2) gives

\[
U\setminus D\subseteq K_j=U\setminus C_j
\]

for some `j`, equivalently `C_j subseteq D`. Complements of the large traces
form an antichain, so the recognition lemma applies.

These two equalities are an exact arbitrary-`U` blocker reduction, not a
bounded atom enumeration.

## 5. Exclusion of the surviving `(4,3)` split

`PROVED`: every transversal of `\mathcal S` has size at least four. Any
transversal contains an inclusion-minimal transversal because `U` is finite;
by `\mathcal C=B(\mathcal S)`, that minimal transversal is one of the `C_j`,
and (4) gives its size at least four.

`PROVED`: the four sets `S_1,S_2,S_3,S_4` are pairwise disjoint. If, for
example, `x` belonged to two of them, choose one point from each of the other
two nonempty small sets. Those at most three chosen points would meet all four
small sets, contradicting the preceding transversal lower bound.

`PROVED`: choose one point `x_i` from each `S_i`. Because the four sets are
pairwise disjoint,

\[
\{x_1,x_2,x_3,x_4\}
\]

is an inclusion-minimal transversal of `\mathcal S`: removing `x_i` leaves
`S_i` unhit. Different choices give different transversals. Hence

\[
|B(\mathcal S)|\ge\prod_{i=1}^4|S_i|\ge2^4=16.             \tag{8}
\]

But `\mathcal C=B(\mathcal S)` and `|\mathcal C|=3`, contradicting (8). Thus
the unique count-surviving split cannot satisfy the universal cover.

`PROVED` (local second-layer theorem): for any finite `U`, every antichain
interface satisfying small size at least two, large-complement size at least
four, cross-intersection, and the universal oriented cover has at least eight
members. If it had at most six, `p=2/5` would give

\[
1\le \mathbb E Z\le\frac4{25}|A|\le\frac{24}{25},
\]

a contradiction; if it had seven, Sections 3--5 give the blocker
contradiction. Equivalently, for the actual layer one may combine the equality
exclusion with the frozen `|A_2|>=7` bound.

Applying this local theorem to the actual second canonical layer gives

\[
|A_2|\ge8.                                                 \tag{9}
\]

`PROVED` (independent structural cross-check): Prover C derives directly,
without the Bernoulli classification, that the two sides are mutual blockers,
that `a>=4,b>=2`, and that all possibilities with `a+b=7` are impossible.
Prover B independently proves the residual four-small/three-complement
transversal theorem by a six-pattern exact blocker count. Neither independent
route is needed to fill a gap in Sections 3--5.

## 6. Dual bound for `A_4`

`PROVED`: the local interface for `A_4` has small generators `S` with
`|S|>=4` and large traces `K` whose complements `C=U\setminus K` have
`|C|>=2`.

For `R'=U\setminus R`, transform the interface by taking

```text
new small generators: C = U\K,
new large traces:     U\S.
```

The new small generators have size at least two, and the complements of the
new large traces have size at least four. Moreover,

\[
S\subseteq R\iff R'\subseteq U\setminus S,
\qquad
R\subseteq K\iff U\setminus K\subseteq R'.
\]

Thus the transformed system satisfies the exact `A_2` cover for every
`R' subseteq U`. Complementing reverses same-side containment, and the cross
condition is unchanged. Applying the local second-layer theorem to the
transformed system gives

\[
|A_4|\ge8.                                                 \tag{10}
\]

This is a direct finite-set duality; it does not assume a fixed core size.

## 7. Global sum

`PROVED`: insert (9)--(10) into the accepted frozen G4 layer framework:

\[
\begin{aligned}
|F|
&=\sum_{i=0}^6|A_i|\\
&\ge1+6+8+9+8+6+1\\
&=39.
\end{aligned}
\]

The chosen ground set is in the eventual stable range and `F` is minimum,
so

\[
\operatorname{sat}(7)=\operatorname{sat}(n,7)=|F|\ge39.
\]

This is a global eventual lower bound, not a fixed-core template-class claim.

## 8. Boundary and quantifier audit

- `PROVED`: `U` is an arbitrary finite set. No upper bound on `|U|` occurs.
- `PROVED`: empty small or large sides are included in the eight-split table
  and are excluded with exact rational witnesses.
- `PROVED`: nonuniform sizes and sizes strictly above the lower bounds are
  allowed. They only decrease the Bernoulli event caps, while the blocker
  proof uses only `|S_i|>=2` and `|C_j|>=4`.
- `PROVED`: repeated point-incidence patterns are allowed; (8) counts actual
  distinct choices. Exact duplicate members cannot occur in an antichain set
  family, and no multiset interpretation is used.
- `PROVED`: all core subsets `R`, including `empty` and `U`, occur in (2).
- `PROVED`: same-side antichains are used exactly in the two blocker
  recognition steps. Cross-antichain is used exactly as cross-intersection.
- `PROVED`: no floating-point calculation, division by a variable, limit,
  compactness, finite-`q` extrapolation, SAT certificate, or Formalizer is
  used.
- `PROVED`: the direct `A_4` transformation preserves every quantifier and
  does not assume complement symmetry of a particular family.

## 9. Experimental and isolation record

`COMPUTED`: the isolated Experimentalist searched both blocker-feasible
splits for every `q=0,...,10`; all runs returned `UNSAT`, with no `UNKNOWN`.
Two independent semantic validators and positive/negative controls passed.
The incidence-pattern quotient reports blocker-count lower bound 16 for the
two structural equality cases. These results remain `COMPUTED` because there
is no external UNSAT certificate or formal arbitrary-`U` reduction.

`DEFINITION`: the dedicated Prover and Experimentalist role launchers each
failed before reading materials because their fixed model was unavailable.
Four compatible isolated replacements completed under the identical scope.
The startup failures are not counted as research routes.

| Effective route | Frozen output SHA-256 | Result |
|---|---|---|
| Prover A | `24414500063e4711b97a9c4e83bb068b891a38590cf55ccaed075631048005bb` | exact split classification; only `(4,3)` survives |
| Prover B | `8449e6cfac35afe736404a41a22788e8b0537b80cfd2bc24cf7ab3e0534f64ad` | residual transversal theorem `PROVED` |
| Prover C | `45acf9658d2e4371adcdb7e633fafa902e615ded4f359a65baa17f043731fc88` | full `A_2>=8` independently `PROVED` |
| Experimentalist report | `9ff4ad0ee0063b306f203597ffe1fd068f03a879510d9b5b86e13dad2f95688f` | `COMPUTED`, no witness |

## 10. Control-panel correction and dependency ledger

`DEFINITION`: this gate uses the binding control-panel baseline correction
recorded in `section0-freeze.md`: the direct Gerbner et al. general theorem
gives `sat(7)>=9`, while Martin--Veldt Theorem 18 is not used as a `k=7`
baseline. This correction changes neither P0054-C17 nor any step above.

| Node | Status | Dependency |
|---|---|---|
| frozen global canonical framework | `PROVED` | accepted P0054-C17 proof and P0054-C7 |
| exact seven-split classification | `PROVED` | (1)--(2), rational Bernoulli expectation |
| mutual blocker reduction | `PROVED` | antichains, cross-intersection, universal cover |
| exclusion of `(4,3)` | `PROVED` | mutual blockers and size lower bounds |
| `|A_2|>=8` | `PROVED` | frozen `|A_2|>=7` plus equality exclusion |
| `|A_4|>=8` | `PROVED` | direct complemented-interface duality |
| `sat(7)>=39` | `PROVED` | frozen remaining layer bounds and stable quantifier |

```text
FIRST_UNCERTAIN_MATHEMATICAL_STEP: NONE_WITHIN_FROZEN_DEPENDENCIES
UNRESOLVED_MATHEMATICAL_DEPENDENCIES: NONE
COUNTEREXAMPLES: NONE
FINITE_PATTERN_REDUCTION_USED_AS_PROOF: NO
REFEREE_STATUS: NOT_YET_RUN
CLAIMS_OR_STATUS_MODIFIED: NO
```
