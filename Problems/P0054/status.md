# P0054 status

```text
RUN_MODE: EXACT_VALUE_INTEGRATION
CURRENT_GATE: P0054_G4_14_EXACT_VALUE_PROMOTION
GATE_VERDICT: EXACT_STABLE_VALUES_FORMALIZED
WORKFLOW_STATUS: SOLVED_CANDIDATE
EPISTEMIC_STATUS: FORMALIZED_EXACT_STABLE_VALUES
FORMAL_VERIFICATION_DATE: 2026-07-30
TARGET: IsStableSaturationNumber 6 30; IsStableSaturationNumber 7 55
CORE_SIZES: ARBITRARY_FINITE_U_IN_GLOBAL_CANONICAL_DECOMPOSITION
KNOWN_CONTROL: PUBLISHED_56_CONSTRUCTION
PROVED_GLOBAL_RESULT: sat(6) = 30; sat(7) = 55
FORMALIZED_GLOBAL_RESULTS: IsStableSaturationNumber 6 30; IsStableSaturationNumber 7 55
NOVELTY_WORDING_ALLOWED: NO
GLOBAL_sat7_CLAIM_ALLOWED: YES_FORMALIZED_STABLE_EXACT_VALUE_55
FORMALIZER_USED_IN_G4: NO
FORMALIZER_USED_IN_G4_2: NO
FORMALIZER_USED_IN_G4_3: NO
FORMALIZER_USED_IN_G4_4: NO
FORMALIZER_USED_IN_SAT6_LOCAL_CORE: YES
FULL_SAT6_THEOREM_FORMALIZED: YES
FORMALIZER_USED_IN_G4_13_LOCAL_KERNEL: YES
FULL_SAT7_THEOREM_FORMALIZED: YES
EXACT_VALUE_LEAN: FORMALIZED
FULL_LAKE_BUILD: PASSED_17488_JOBS
FORMAL_MAIN_CHECK: PASSED
FINAL_AXIOMS: propext; Classical.choice; Quot.sound
FORBIDDEN_TOKEN_AND_BYPASS_SCAN: ZERO_HITS
```

## Evidence boundary

Z3 is used only to calibrate feasibility.  `SAT` becomes useful only after two
independent semantic verifiers accept the extracted family.  `UNSAT` is not a
theorem unless an independently checkable certificate and the encoding
reduction are both supplied.  `UNKNOWN` or timeout is no mathematical evidence.

The repository already contained uncommitted P0053 F5 manuscript files when
P0054 began.  P0054 is isolated from those paths; this run is not a clean-
baseline release gate.

## Current mathematical results

For `|C|=7`, the exact minimum in the full stated template class is 56.  The
lower bound is backed by a deterministic CNF and independently verified DRAT
proof; the upper bound is the published 56 construction accepted by two
semantic verifiers.  This is not a proof that `sat(7)=56` globally.

For `|C|=8`, an explicit system of size 55 was extracted.  The seven layer
sizes are `(1,6,12,17,12,6,1)`.  It is accepted by the universal signature
verifier, the full-ground layer verifier, the older integer-bitmask union
verifier, and the older `frozenset` DAG union verifier.  Hence the family is a
saturated 7-Sperner family and proves `sat(7) <= 55`.

G4.10 and G4.11 exclude the total-52 and total-53 equality profiles. G4.12
then reduces every possible 54-member family to the Fano profile or the
sixteen-member middle profile. It excludes the Fano adjacent splits and every
middle split `(5,11)`, `(6,10)`, `(7,9)`, `(8,8)`, together with their blocker
duals. The arbitrary-finite reductions preserve inactive points, repeated
incidence patterns, parallel actual points, and nonuniform row sizes.

The isolated G4.12 Referee returned `ACCEPT` with
`FIRST_INVALID_STEP: NONE`. The post-Referee gate replayed every bound source
and output and reported `178 passed`. Therefore no 54-member family survives,
and the upper construction gives the internal exact result

```text
sat(7) = 55.
```

## Lean formalization

The complete exact-value chain first closed on 2026-07-27 and was revalidated
after the fourth pre-review revision on 2026-07-30. Both exact eventual
statements are `FORMALIZED`. Lean accepts the public theorems

```text
AiMathLab.P0054.Sat6StableExact.sat_six_eq_thirty
  : IsStableSaturationNumber 6 30
AiMathLab.P0054.Sat7StableExact.sat_seven_eq_fifty_five
  : IsStableSaturationNumber 7 55
```

`IsStableSaturationNumber k s` is a proposition. It states that some threshold
`N` works for every `n>=N`: a saturated `k`-Sperner family of cardinality `s`
exists on `Fin n`, and every such family has cardinality at least `s`. Thus the
Lean result is not evaluation of a numerical function named `sat`.

The six-layer proof uses the explicit threshold `3*2^30`. The seven-layer
proof uses `3*2^55`. Both constructions are parameterized over the remaining
homogeneous atom and transported to `Fin n`. The lower theorems quantify over
every saturated family on each ground past the threshold.

The concrete eleven-point size-55 certificate and the G4.13 five-row kernel
remain formalized components of the final dependency graph. They are no
longer the boundary of the Lean result.

The command `lake build AiMathLab AiMathLab.P0054Sat7StableExact` completed
all 17488 jobs. The command
`lake env lean Problems/P0054/formal/Main.lean` also succeeded. The final
theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The forbidden
token and bypass scan over Lean sources returned zero hits.

Novelty and priority remain `UNKNOWN`.

## Manuscript preparation

The English and Simplified-Chinese internal-review manuscripts are maintained
at `Problems/P0054/paper/manuscript/main.tex` and `main.zh-Hans.tex`. Rendered
copies are placed at `output/pdf/P0054-sat6-sat7-English.pdf` and
`output/pdf/P0054-sat6-sat7-zh-Hans.pdf`.  A self-contained Elsevier CAS
package for the Journal of Combinatorial Theory, Series A is maintained at
`Problems/P0054/paper/submission/jcta/`, with its rendered draft at
`output/pdf/P0054-sat6-sat7-JCTA-submission-draft.pdf`.

The manuscripts contain the exact values `sat(6)=30` and `sat(7)=55`; the
arbitrary-finite blocker reductions and exhaustive 54-member profile
exclusion; the explicit 55-member construction and composition consequence;
the seven-core class certificate boundary; and the exact scope of the Lean
formalizations.

The manuscript and local JCTA package are
`LOCAL_V1.1_ARTIFACT_VERIFIED_PUBLICATION_PENDING`; this does not mean that a
submission has occurred. Author affiliation, ORCID, funding, and
competing-interest fields are complete. On 29 July 2026, the author confirmed that the manuscript had
not been published and was not under consideration elsewhere. The author also
reported completion of an external specialist review; no private report is
archived here, and this is not represented as journal peer review. The final
pre-submission search is recorded in
`literature/final-prepublication-audit-2026-07-29.md` and found no public
equivalent in its bounded scope. Remaining public actions are a GitHub
v1.1.0 release and a new immutable Zenodo version for this exact revision.
P0054-C5, P0054-C9, P0054-C24, and P0054-C29 remain `UNKNOWN`; no unqualified
novelty or priority wording is authorized.

On 30 July 2026, the fourth-pre-review revalidation passed the single-process,
two-target full Lake build (17,488 jobs), the independent `Main.lean` entry
point, and the forbidden-construct scan.  The JCTA, ordinary English, Chinese,
and Supplement PDFs have 16, 17, 17, and 15 pages, respectively.  PDF text
extraction and page-by-page visual inspection passed, including the worked
interface, corrected crosswalk, revised bounded-search date, and corrected
common-prefix punctuation. The authoritative `release/verify-core.sh` passes
the core replay and 42 P0054 tests, preserves full logs, and emits a JSON
summary with commands, exit codes, 4,530 nonfatal Lake warnings, theorem
types, and the expected axiom boundary. Its controlled failure test returned
42 and reported `FAIL`. The revision-synchronized local v1.1.0 package passes
its integrity check; its core script is byte-identical, but a new default-path
empty-cache package replay was not repeated after this document-only change.
The 29 July supporting gate remains the most recent replay of all 178
repository tests; those program and certificate sources were not changed in
this document-facing revision.

## G2 size-54 evidence boundary

This section is a historical G2 record and is superseded by the accepted
G4.12 proof.

The exact proof is in `proof/size54-oriented-reduction.md`.  Reproducible
reports and CNFs are under `experiments/size54-g2/`.  No run produced a
candidate, a complete UNSAT result, or a proof certificate.  Consequently:

- G2 proved only `sat(7) <= 55`;
- G2 did not prove `sat(7) <= 54`;
- G2 did not exclude 54, even inside the eight-core template class;
- G4.12 later superseded this boundary and proved the exact value.

## G3 structural lower-bound results

Saturation and the predecessor condition imply a matching successor condition:
every lower-layer member lies strictly below a member of the next layer.  Thus
every selected template lies on a full seven-layer chain.  For an eight-point
core, layer `i` is confined to template ranks `i,...,i+3`, reducing the complete
model from 3,584 to 1,934 primary variables.

Four deterministic single-layer CNFs and four DRAT-trim-verified proofs establish
the exact independent layer minima

```text
(1, 6, 12, 14, 12, 6, 1).
```

The middle upper bound uses an independently checked 14-member saturated layer;
the other upper bounds occur in the verified 55-member family.  These minima
sum to 52, so every target-54 candidate has only two possible slack members.

The displayed sharp 14-member middle layer cannot extend to a full target-54
system: a 42,951,282-byte DRAT proof was independently accepted.  This is a
strict result about that fixed layer, not a classification of all sharp middle
layers.

The unrestricted reduced target-54 instance remained `UNKNOWN` after 1,800
seconds.  All 28 complete two-slack profiles also remained `UNKNOWN` at 60
seconds.  Therefore, at the end of G3, the eight-core class minimum remained
either 54 or 55, the best global upper bound remained `sat(7)<=55`, and no
new global lower bound had yet been added.

## G4 global lower bound

The eventual stable saturation number satisfies `sat(7)>=37`.  On a stable
ground set with `n>2^55`, a minimum endpoint-normal saturated family has a
homogeneous atom.  Its canonical decomposition has seven saturated-antichain
layers.  The verified layer lower bounds are

```text
(1, 6, 7, 9, 7, 6, 1),
```

whose sum is 37.  The internal bounds use an exact oriented Bernoulli cover;
the middle equality case is excluded pointwise, not by floating-point
rounding or finite-core solver output.

Two isolated offline Referees independently reconstructed the global
quantifiers and the internal covering argument and both returned `ACCEPT`.
No repair cycle was used.  The proof is global rather than restricted to the
G0--G3 common-block finite template classes: the common block is forced for a
minimum family after choosing a sufficiently large stable ground set.

The printed Martin--Veldt Lemma 17 specializes numerically to the same
internal bounds, but its proof's strict exponential comparison degenerates
to equality at `k=7,i=3`.  The G4 proof independently repairs that equality
seam.  This supports no novelty, priority, `WORLD_FIRST`, or best-known
wording.  The dedicated-negative-search result remains only
`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`.

No stronger bound, Lean formalization, size-54 search, publication, release,
commit, or push was attempted in G4.  The exact value of `sat(7)` remains
`UNKNOWN`.

## G4.2 stronger global lower bound

`PROVED`: every second internal layer in the frozen G4 global canonical
decomposition has size at least eight.  If a seven-member layer has `a` small
and `b` large members, exact rational Bernoulli inequalities eliminate every
split except `(a,b)=(4,3)`.  No floating-point comparison is used.

`PROVED`: in the remaining split, the four small generators and the three
large-trace complements would have to be mutual blockers.  Complement size at
least four forces the four small generators to be pairwise disjoint, which
creates at least `2^4=16` distinct minimal transversals, contradicting the
three complements.  This argument quantifies arbitrary finite `U`; it is not
a finite-core enumeration.

`PROVED`: complementing the core variable and exchanging the two oriented
sides transfers the same local theorem to the fourth internal layer.  Thus
the accepted layer bounds are

```text
(1, 6, 8, 9, 8, 6, 1),
```

whose sum proves `sat(7)>=39`.

`PROVED`: two isolated, read-only, offline compatible Referees independently
reconstructed the probability classification, blocker reduction, dual
interface, global canonical dependencies, and stable-value quantifier.  Both
returned `ACCEPT`; no repair cycle was used.

`COMPUTED`: the isolated Experimentalist found no seven-member `A_2` model for
`|U|=0,...,10` and recorded a canonical incidence-pattern quotient with two
independent semantic validators.  These solver and quotient outputs remain
`COMPUTED` and are not dependencies of the proof.

`DEFINITION`: the G4.2 control panel uses the corrected published baseline
`sat(7)>=9` from the direct Gerbner et al. general theorem.  Martin--Veldt
Theorem 18 is not used as a `k=7` baseline under this gate's recorded `k>7`
condition.  This wording correction changes neither P0054-C17 nor its proof.

No Formalizer, network access, adjacent-layer fallback, size-54 search,
publication, release, stage, commit, or push was used in G4.2.  At the close
of that historical gate, the exact value of `sat(7)` remained `UNKNOWN`; the
later exact-value and Lean gates recorded above supersede that boundary.

## G4.3 stronger global lower bound

`PROVED`: for arbitrary finite `U`, let the ordinary set families
`mathcal S` and `mathcal C` satisfy

```text
mathcal S = B(mathcal C),
mathcal C = B(mathcal S),
|S| >= 2 for every S in mathcal S,
|C| >= 4 for every C in mathcal C.
```

Then `|mathcal S|+|mathcal C|>=9`.  The private-witness lemma gives
`|T|<=|mathcal H|` for every `T in B(mathcal H)`, reducing a putative
eight-member pair to `(4,4)`, `(5,3)`, or `(6,2)`.  The three splits are
excluded respectively by four-family transversal counting, an exact
three-family incidence-pattern count giving at least twelve blockers, and
two-family cross-pair counting giving at least sixteen blockers.  Empty
sides, repeated incidence patterns, nonuniform member sizes, and arbitrary
finite ground sets are included in these arguments.

`PROVED`: the frozen G4.2 oriented-cover interface recognizes the second
internal layer as such a mutual-blocker pair, hence `|A_2|>=9`.  Exchanging
the two blocker sides in the complementary fourth-layer interface gives
`|A_4|>=9`.  Together with the accepted other layer bounds,

```text
(|A_0|,...,|A_6|) >= (1,6,9,9,9,6,1),
```

whose sum proves `sat(7)>=41`.

`PROVED`: two isolated, read-only, offline compatible Referees independently
reconstructed all three split exclusions, blocker minimality, complementary
side exchange, global layer summation, and eventual-stability quantifier.
Both returned `ACCEPT`; no repair cycle was used.

`COMPUTED`: the isolated Experimentalist's incidence-pattern search found no
admissible pair of total size 8, 9, or 10 and passed two independent semantic
validators on its recorded finite validation domain.  These finite outputs
are not dependencies of the proof and do not establish a stronger general
lower bound or the exact value of the local parameter.

`PROVED`: the post-acceptance stronger exploration gives the strict interval
`9<=m(2,4)<=12`.  The upper bound is witnessed by the edge clutter of two
vertex-disjoint four-cycles: its blocker consists of the four unions of one
bipartition class from each cycle, so the two blocker sides have sizes eight
and four and member-size minima two and four.  The exact local value remains
`UNKNOWN`; no unproved product inequality or finite negative search is used.

No Formalizer, network access, old size-54 CNF, publication, release, stage,
commit, or push was used in G4.3.  At the close of that historical gate, the
exact local parameter and the exact value of `sat(7)` remained `UNKNOWN`
unless separately closed by a general proof.  G4.4 and the final exact-value
gate later supplied those separate closures.

## G4.4 exact local parameter

`PROVED`: for every finite admissible `(2,4)` mutual-blocker pair
`(mathcal S,mathcal C)`,

```text
|mathcal S| |mathcal C| >= 32
and
|mathcal S| + |mathcal C| >= 12.
```

The proof is purely combinatorial.  A residual decomposition proves that four
members of minimum size four have at least eight blockers.  Intersection-graph
and actual-point multigraph classifications prove that five generators of
minimum size two have at least eight blockers and six such generators have at
least six blockers whenever every transversal has size at least four.  Together
with the frozen two-, three-, and four-generator bounds, seven cardinality
cases exhaust all admissible pairs and prove the product inequality.  The
integer step uses `128 > 11^2`, with no floating-point approximation.

`PROVED`: the edge clutter of two vertex-disjoint four-cycles and the four
unions of their bipartition classes form a mutual-blocker pair of cardinalities
eight and four.  Therefore

```text
m(2,4) = 12.
```

The six previously unresolved ordered splits `(5,4)`, `(6,4)`, `(5,5)`,
`(7,4)`, `(6,5)`, and `(5,6)` are all excluded by the general combinatorial
lemmas.  The argument allows arbitrary finite `U`, repeated positive
incidence-pattern multiplicities, empty incidence classes, nonuniform member
sizes, and ordinary set-family rather than multiset cardinality.

`PROVED`: applying the exact local parameter independently to the frozen
`A_2` and `A_4` mutual-blocker interfaces gives

```text
(|A_0|,...,|A_6|) >= (1,6,12,9,12,6,1),
```

whose exact integer sum proves `sat(7)>=47`.

`PROVED`: two isolated, read-only, offline compatible Referees independently
reconstructed the residual blocker bijection, all small-generator
classifications, the six split exclusions, the twelve-member witness, and the
global layer interface.  Both returned `ACCEPT`; no repair cycle was used.
The dedicated Referee role launches failed before accessing material because
their fixed runtime model was unavailable, so their compatible replacements
are recorded explicitly rather than silently counted as dedicated runs.

`COMPUTED`: an isolated exact incidence-pattern experiment completed all 15
admissible ordered splits of totals 9, 10, and 11, reporting
`UNSAT_COMPUTED` after 147,340,811 DFS nodes.  A deterministic structural
replay matched, two blocker implementations agreed on their validation domain,
and no timeout occurred.  These outputs have neither a complete independently
checkable UNSAT certificate nor a second complete enumerator, so they remain
`COMPUTED` and are not dependencies of P0054-C20.

No Formalizer, post-freeze network access, old size-54 CNF, publication,
release, stage, commit, or push was used in G4.4.  At the close of that
historical gate, the exact value of `sat(7)` remained `UNKNOWN`; later gates
closed the exact value.  Novelty and priority remain `UNKNOWN`.

## G4.10 total-52 exclusion

`PROVED`: the equality profile

```text
(1, 6, 12, 14, 12, 6, 1)
```

is impossible. The middle 14-member blocker pair reduces to the asymmetric
splits `(5,9)`, `(6,8)` and their duals, or the central split `(7,7)`. The
asymmetric splits are excluded by arbitrary-finite loop-multigraph reductions.
The central split is forced to be the Fano plane, whose adjacent equality
layer is impossible. The isolated Referee returned `ACCEPT`. Hence
`sat(7)>=53`.

## G4.11 total-53 exclusion

`PROVED`: after the G4.10 exclusion, a 53-member family would have profile

```text
(1, 6, 12, 15, 12, 6, 1).
```

The middle blocker pair splits as `(5,10)`, `(6,9)`, `(7,8)`, or a dual.
Point-degree reductions, exact three-row formulas, residual blockers, and
finite kernel classifications exclude every split on an arbitrary finite
trace ground set. The repaired proof received `ACCEPT` with
`FIRST_INVALID_STEP: NONE`. Hence `sat(7)>=54`.

## G4.12 exact value

`PROVED`: every possible 54-member profile is impossible. The slack reduction
leaves exactly

```text
(1, 6, 13, 14, 13, 6, 1)
(1, 6, 12, 16, 12, 6, 1).
```

The first profile has a Fano middle pair. Its adjacent splits `(7,6)`, `(8,5)`,
and `(9,4)`, together with their duals, are impossible. The second profile has
a middle blocker pair of total sixteen. A probabilistic cover forces a
three-point row, and the splits `(5,11)`, `(6,10)`, `(7,9)`, `(8,8)`, plus
their duals, are all excluded.

Every finite enumeration appears after a proved arbitrary-finite reduction.
Independent implementations reproduced the saved outputs byte for byte. The
manifest bound 36 objects, all hashes matched, and the isolated Referee
returned `ACCEPT`. Combining the exclusion with P0054-C7 gives

```text
sat(7) = 55.
```

## G4.13 local Lean strengthening

`FORMALIZED`: Lean proves the five-row degree-three kernel no-completion
theorem. In the current dependency graph it is used in the total-fifteen
`(7,8)` branch; the total-sixteen `(8,8)` branch is closed separately by
`G420.eightEight_impossible`. The local theorem includes unconditional
residual bounds and all five pair-graph shapes. No placeholder, unsafe
shortcut, or new axiom occurs.

`HISTORICAL_GATE_STATUS`: at G4.13, the other G4.12 branches and the global
canonical reduction remained outside Lean. This local theorem did not by
itself formalize the exact stable value.

The later exact-value formalization closed those remaining dependencies. The
current public theorem has type `IsStableSaturationNumber 7 55`.

## G4.14 exact-value promotion

`SOLVED_CANDIDATE`: P0054-C25 through P0054-C28 record the accepted lower-bound
chain and exact value. P0054-C28 is now `FORMALIZED` by the final stable-number
theorem. The prior-art audit found no public equivalent in its recorded scope,
but this is a bounded negative search. P0054-C29 remains `UNKNOWN`; only
independent human review may promote the workflow to `SOLVED`.

## Exact value at six layers

`FORMALIZED`: Lean proves

```text
IsStableSaturationNumber 6 30.
```

Equivalently, there is a threshold after which the exact minimum is 30 on
every labelled finite ground. This is an existential eventual-stability
statement, not evaluation of a Lean numerical function. In conventional
mathematical notation, it states

```text
sat(6) = 30.
```

The new lower-bound ingredient is the arbitrary-finite-ground local theorem
`m(2,3)=9`. Every admissible mutual-blocker pair with member-size minima two
and three has total cardinality at least nine. A six-point pair with side
cardinalities five and four attains the bound.

`FORMALIZED`: Lean proves the local lower bound, both blocker equalities for
the witness, its side cardinalities, and its member-size conditions. The Lean
result quantifies over every finite ground set and uses no `sorry`, `admit`,
new `axiom`, `unsafe`, or `native_decide`.

`PROVED + LITERATURE`: the independent natural-language proof chooses a stable
ground set larger than `2^30`, applies the homogeneous-atom and canonical-layer
theorems, and uses the layer bounds

```text
(1, 5, 9, 9, 5, 1).
```

Their sum gives the lower bound 30. Morrison--Noel--Scott Proposition 20 gives
the matching upper bound on every ground set of size at least eight.

`COMPUTED`: the companion incidence-pattern search exhausts every ordered
split of total at most eight and verifies the nine-member witness. It is not a
proof dependency.

The literature audit returned
`NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE`. Novelty, priority, and external
expert acceptance remain `UNKNOWN`. The final Lean theorem uses the explicit
threshold `3*2^30` and formalizes both attainment and optimality past it.
