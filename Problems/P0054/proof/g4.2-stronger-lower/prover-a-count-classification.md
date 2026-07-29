# P0054 G4.2 isolated Prover A: exact count classification

```text
ROLE: COMPATIBLE_ISOLATED_PROVER_A
SCOPE: EXACT_BERNOULLI_COUNT_CLASSIFICATION_FOR_a_plus_b_equals_7
NETWORK: FORBIDDEN; NOT_USED
FORMALIZER: FORBIDDEN; NOT_USED
OTHER_G4_2_AGENT_OUTPUTS: NOT_READ
OLD_STATUS_CLAIMS_PROTECTED_FILES: NOT_MODIFIED
```

## 1. Frozen boundary and assumptions

`COMPUTED`: this report used only the following four inputs. The first and
third hashes match the values recorded for them in the Section 0 freeze; the
other two hashes record the bytes observed by this Prover.

| Input | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/proof/g4.2-stronger-lower/frozen-subproblem.md` | `2149cbed8621e7643307e8c508301d898e25e3a661bc2b1f05910354f2ba2a42` |
| `Problems/P0054/proof/g4-global-lower/candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| `Problems/P0054/experiments/g4.2-stronger-lower/section0-freeze.md` | `6551eda020048d809f5cd9f8d85908cc821a1adc2c9d8c026960354533d9d5d4` |

`DEFINITION` (event hypotheses): let `U` be a finite set. There are `a`
indexed small events with generators `S_i subseteq U`, where `|S_i|>=2`,
and `b` indexed large events with traces `K_j subseteq U`, where
`C_j=U\K_j` satisfies `|C_j|>=4`. Assume

```text
a,b are nonnegative integers,    a+b=7,
```

and assume the pointwise oriented cover

\[
 Z(R):=\sum_{i=1}^{a}{\bf1}[S_i\subseteq R]
      +\sum_{j=1}^{b}{\bf1}[R\subseteq K_j]\geq 1
 \qquad(R\subseteq U).                                      \tag{1}
\]

`DEFINITION`: for a rational `p` with `0<p<1`, put

\[
 F_{a,b}(p):=a p^2+b(1-p)^4.                                \tag{2}
\]

## 2. Exact necessary probability inequality

`PROVED`: under the event hypotheses, every rational `0<p<1` satisfies

\[
 1\leq F_{a,b}(p).                                           \tag{3}
\]

**Proof.** Include each element of the finite set `U` in `R` independently
with probability `p`. Exact finite-product probabilities give

\[
 \Pr(S_i\subseteq R)=p^{|S_i|},\qquad
 \Pr(R\subseteq K_j)=(1-p)^{|C_j|}.
\]

Taking expectations in the pointwise inequality (1), and then using
`0<p<1`, gives

\[
 1\leq \mathbb E Z(R)
   =\sum_i p^{|S_i|}+\sum_j(1-p)^{|C_j|}
   \leq a p^2+b(1-p)^4.
\]

All quantities are rational. No independence or disjointness among the
events is used; independence is used only among the element-inclusion
choices defining `R`. This proves (3). `QED`

## 3. Classification theorem

`PROVED` (exact count classification): for nonnegative integers `a,b` with
`a+b=7`,

\[
 \bigl(\forall p\in\mathbb Q,\ 0<p<1:\ 1\leq F_{a,b}(p)\bigr)
 \quad\Longleftrightarrow\quad (a,b)=(4,3).                  \tag{4}
\]

### 3.1 Exact counterexamples for seven splits

`REFUTED`: each row marked `REFUTED` fails the universal condition in (4)
at the displayed rational `p`. The final comparison explicitly compares
the numerator with its positive denominator.

| `a` | `b` | exact rational `p` | exact value of `F_{a,b}(p)` | split status |
|---:|---:|---:|---:|---|
| 0 | 7 | `1/2` | `7/16 < 16/16 = 1` | `REFUTED` |
| 1 | 6 | `1/2` | `10/16 < 16/16 = 1` | `REFUTED` |
| 2 | 5 | `1/2` | `13/16 < 16/16 = 1` | `REFUTED` |
| 3 | 4 | `2/5` | `3(4/25)+4(81/625)=300/625+324/625=624/625 < 625/625 = 1` | `REFUTED` |
| 4 | 3 | every rational `0<p<1` | proved strictly greater than `1` in Section 3.2 | `PROVED` |
| 5 | 2 | `1/3` | `5(1/9)+2(16/81)=45/81+32/81=77/81 < 81/81 = 1` | `REFUTED` |
| 6 | 1 | `1/3` | `6(1/9)+16/81=54/81+16/81=70/81 < 81/81 = 1` | `REFUTED` |
| 7 | 0 | `1/3` | `7/9=63/81 < 81/81 = 1` | `REFUTED` |

The table is exhaustive because the eight displayed pairs are exactly the
nonnegative integer solutions of `a+b=7`.

### 3.2 Exact proof for the unique surviving split

`PROVED`: `F_{4,3}(p)>1` for every real `p`, hence in particular for every
rational `0<p<1`.

**Proof.** Put `q=1-p` and `r=5/8`. The exact polynomial identity

\[
 q^4-4r^3q+3r^4
   =(q-r)^2(q^2+2rq+3r^2)
   =(q-r)^2\bigl((q+r)^2+2r^2\bigr)\geq0
\]

implies, using `r^3=125/512` and `r^4=625/4096`,

\[
 3q^4\geq \frac{375}{128}q-\frac{5625}{4096}
       =\frac{6375}{4096}-\frac{375}{128}p.                 \tag{5}
\]

Therefore an exact completion of the square gives

\[
\begin{aligned}
 F_{4,3}(p)
 &=4p^2+3(1-p)^4\\
 &\geq4p^2-\frac{375}{128}p+\frac{6375}{4096}\\
 &=4\left(p-\frac{375}{1024}\right)^2
   +\frac{267375}{262144}\\
 &=1+4\left(p-\frac{375}{1024}\right)^2
   +\frac{5231}{262144}>1,
\end{aligned}
\]

because `5231>0` and `262144>0`. This proves the surviving direction of
(4), while Section 3.1 proves all seven exclusions. `QED`

`PROVED` (conditional application): every event system satisfying Section 1
has

```text
(a,b) = (4,3).
```

Indeed, Section 2 supplies the universal necessary condition and the
classification theorem has only this one solution.

## 4. Boundary and direction audit

- `PROVED` (empty sides): the sums in (1) allow `a=0` or `b=0`; an empty
  sum is zero. The table separately refutes `(0,7)` and `(7,0)`. Both sides
  cannot be empty because `a+b=7`.
- `PROVED` (sizes strictly above the lower bounds): for `0<p<1`, if
  `|S_i|>2` then `p^{|S_i|}<p^2`, and if `|C_j|>4` then
  `(1-p)^{|C_j|}<(1-p)^4`. Thus the displayed powers are **upper** bounds
  on event probabilities. Larger actual exponents can only lower
  `E[Z]`; they cannot repair any refuted split. For `(4,3)`, however, they
  may make the exact expectation smaller than the coarse cap, so survival
  of (3) does not establish coverage.
- `PROVED` (repetition and overlap): linearity of expectation counts indexed
  events with multiplicity. The argument remains valid if two indexed
  events happen to coincide, and it never assumes that event sets are
  disjoint or independent. In the original set-family setting exact
  duplicate members are absent, but that extra fact is not needed here.
- `PROVED` (finite ground set): the product distribution and both event
  probabilities are exact on every finite `U`; no limit, asymptotic step,
  division, or continuity argument is used. Every excluding `p` is an
  interior rational.
- `PROVED` (necessary, not sufficient): the implication established here is
  `pointwise cover => exact expectation inequality => coarse count
  inequality`. Neither reverse implication was established. In particular,
  `(4,3)` is only the unique count split **not excluded** by the coarse
  inequality; this report does not assert that a covered incidence system
  with that split exists.
- `DEFINITION` (unused extra structure): the cross-incidence condition
  `S_i cap C_j != empty` coming from the antichain hypothesis, and all finer
  incidence information, are intentionally not analyzed in this isolated
  count-classification report.

## 5. Relation to frozen P0054-C17 and the stronger target

`PROVED` (dependency direction): the algebraic equivalence (4) itself does
not use P0054-C17. Its application to a hypothetical seven-member `A_2`
uses the frozen G4 setup imported in the permitted inputs: the oriented
cover, `|S|>=2`, `|U\K|>=4`, and `a+b=7`. These are the same local
ingredients by which the frozen G4 candidate proof obtained `|A_2|>=7`.
The Section 0 record says P0054-C17 and the accepted `sat(7)>=37` proof are
frozen; this report neither modifies nor re-proves that claim.

`UNKNOWN` (`THEOREM_A2_CANDIDATE`): this count argument cannot by itself
deduce `|A_2|>=8`. Under the hypothetical equality `|A_2|=7`, it eliminates
seven count splits but leaves `(a,b)=(4,3)`, for which the coarse necessary
inequality actually holds with a positive exact margin for every `p`.
Excluding that remaining split requires information beyond the count-only
Bernoulli cap. No such hypergraph/incidence analysis is attempted here.

## 6. Verdict

```text
COUNT_CLASSIFICATION_STATUS: PROVED
UNIQUE_SPLIT_NOT_EXCLUDED_BY_COARSE_NECESSARY_INEQUALITY: (a,b)=(4,3)
THEOREM_A2_CANDIDATE_STATUS_FROM_THIS_REPORT: UNKNOWN
FIRST_UNCERTAIN_MATHEMATICAL_STEP_WITHIN_COUNT_CLASSIFICATION: NONE
FIRST_UNRESOLVED_STEP_TOWARD_A2_GE_8: EXCLUDE_THE_(4,3)_INCIDENCE_CASE_USING_ADDITIONAL_STRUCTURE
NETWORK_USED: NO
FORMALIZER_USED: NO
OTHER_G4_2_AGENT_OUTPUTS_READ: NO
```
