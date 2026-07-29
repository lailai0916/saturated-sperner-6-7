# Attempt 002: exact Bernoulli bounds for the internal layers

## Scope and verdict

- `DEFINITION`: this note is the isolated Prover B route. It proves only a
  conditional theorem about one saturated antichain with a homogeneous atom.
- `PROVED`: under the hypotheses stated below, the layer-size bounds are
  `7,9,7` for indices `i=2,3,4`, respectively.
- `UNKNOWN`: this note does not establish that the canonical layers of a
  globally minimum saturated 7-Sperner family satisfy these hypotheses. That
  dependency belongs to the separate canonical-decomposition audit.
- `UNKNOWN`: no global lower bound for `sat(7)` is asserted or assembled here.

No floating-point estimates, finite search, or result from another proof
attempt is used.

## Exact conditional theorem

Let `X` be a finite set and let `H` be a subset of `X` with `|H| >= 2`. Put
`C = X \ H`. Let `A` be a saturated antichain in `2^X`, where saturated means
that every member of `2^X \ A` is strictly comparable by inclusion with some
member of `A`. Assume that `H` is homogeneous for `A`: every `A in A` either
satisfies `A cap H = empty` or `H subseteq A`.

Write

```text
S = {A in A : A cap H = empty}       (small members),
L = {A in A : H subseteq A}          (large members),
a = |S|, b = |L|, and m = |A| = a+b.
```

For `i in {2,3,4}`, impose the size conditions

```text
|S| >= i          for every small member S,
|X \ L| >= 6-i    for every large member L.                 (H_i)
```

Here `|S|` in `(H_i)` is the cardinality of a member, not the cardinality of
the collection of small members.

**Conditional internal-layer theorem (`PROVED`).** Under these hypotheses:

```text
i=2  implies  |A| >= 7;
i=3  implies  |A| >= 9;
i=4  implies  |A| >= 7.
```

The proof is self-contained below.

## Lemma 1: pointwise oriented coverage

**Lemma (`PROVED`).** For every `R subseteq C`,

```text
there is S in S with S subseteq R,
or there is L in L with R subseteq L.                        (1)
```

The containments in (1) are intentionally non-strict.

**Proof.** Because `|H| >= 2`, choose a nonempty proper subset `P` of `H` and
form

```text
T_R = R union P.
```

The homogeneity assumption shows that `T_R` is not in `A`: its intersection
with `H` is the nonempty proper set `P`. Saturation therefore gives a member
`A in A` strictly comparable with `T_R`.

If `A` is small, then `T_R subset A` is impossible because `T_R` contains an
element of `H` and `A` contains none. Hence `A subset T_R`, and intersecting
with `C` gives `A subseteq R`. Thus the first alternative in (1) holds.

If `A` is large, then `A subset T_R` is impossible because `A` contains all
of `H` while `T_R` contains only `P`. Hence `T_R subset A`, and intersecting
with `C` gives `R subseteq A`. Thus the second alternative in (1) holds. This
exhausts the two homogeneous types. `QED`

The use of `T_R`, rather than invoking saturation directly on `R`, is
essential: direct comparability with `R` need not have the required
orientation.

## Lemma 2: exact Bernoulli inequality

Fix a rational `p` with `0 < p < 1`. Let `R` be the random subset of `C` in
which each point is independently included with probability `p`. Define the
integer-valued random variable

```text
N_p(R)
  = sum over S in S of 1[S subseteq R]
  + sum over L in L of 1[R subseteq L].                       (2)
```

**Lemma (`PROVED`).** One has the exact inequality

```text
1 <= E[N_p]
  = sum over S in S of p^|S|
  + sum over L in L of (1-p)^|X \ L|.                         (3)
```

**Proof.** Lemma 1 gives `N_p(R) >= 1` for every `R subseteq C`, so
`E[N_p] >= 1`. A small member is a subset of `C`; independence gives

```text
P(S subseteq R) = p^|S|.
```

For a large member `L`, all of `H` is already contained in `L`, so
`C \ L = X \ L`. The event `R subseteq L` says exactly that no point of
`X \ L` is selected. Therefore

```text
P(R subseteq L) = (1-p)^|X \ L|.
```

Linearity of expectation proves the equality in (3), without requiring the
covering events to be disjoint. `QED`

## Exact bounds at `p=2/5,1/2,3/5`

### Index 2

Take `i=2` and `p=2/5`. Since powers of a number in `(0,1)` decrease with the
exponent, `(H_2)` and (3) give

```text
1 <= (4/25)a + (81/625)b
  <= (4/25)(a+b) = (4/25)m.                                  (4)
```

The comparison in the second line is exact because
`81/625 < 100/625 = 4/25`. If `m <= 6`, then the right side of (4) is at most
`24/25 < 1`, a contradiction. Thus `m >= 7`. This proves the proposed
`A_2` bound under the conditional hypotheses.

### Index 4

Take `i=4` and `p=3/5`. Now `(H_4)` and (3) give

```text
1 <= (81/625)a + (4/25)b
  <= (4/25)(a+b) = (4/25)m.                                  (5)
```

Again `m <= 6` would give `1 <= 24/25`, so `m >= 7`. This proves the proposed
`A_4` bound under the conditional hypotheses. No appeal to an unproved duality
transfer is needed.

### Index 3: the initial bound

Take `i=3` and `p=1/2`. Both kinds of event in (3) have probability at most
`(1/2)^3 = 1/8`, whence

```text
1 <= E[N_1/2] <= (a+b)/8 = m/8.                              (6)
```

Thus `m >= 8`. The next section excludes equality.

## The eight-member equality case

Assume for contradiction that `i=3` and `m=8`. For a small member `S` and a
large member `L`, denote their event supports in `2^C` by

```text
U_S = {R subseteq C : S subseteq R},
D_L = {R subseteq C : R subseteq L}.
```

### Every probability reaches its maximum

From (6),

```text
1 <= E[N_1/2] <= 8(1/8) = 1.
```

Hence equality holds throughout. Each of the eight event probabilities is at
most `1/8`; if even one were strictly smaller, their sum would be strictly
smaller than 1. Therefore every event probability is exactly `1/8`. In
particular,

```text
|S| = 3 for every small S,
|X \ L| = 3 for every large L.                               (7)
```

This verifies, rather than assumes, the individual equality conditions.

### The covering multiplicity is exactly one at every `R`

Lemma 1 gives `N_1/2(R) >= 1` pointwise, while the preceding equality gives
`E[N_1/2]=1`. The `p=1/2` distribution has full support: every one of the
finitely many `R subseteq C` has probability `2^(-|C|)>0`. Consequently

```text
N_1/2(R) = 1 for every R subseteq C.                          (8)
```

Indeed, a single value with `N_1/2(R) >= 2` would make the expectation
strictly greater than 1. Thus the eight event supports must form an exact
one-fold partition of `2^C`.

### Same-side supports necessarily intersect

For two distinct small members `S_1,S_2`,

```text
S_1 union S_2 in U_(S_1) cap U_(S_2).
```

The union is a subset of `C`, so the intersection is nonempty. Therefore (8)
allows at most one small member.

For two distinct large members `L_1,L_2`,

```text
empty in D_(L_1) cap D_(L_2).
```

Therefore (8) allows at most one large member.

For completeness, a cross intersection `U_S cap D_L` is nonempty exactly
when `S subseteq L`: one direction follows from an intermediate
`S subseteq R subseteq L`, and the converse uses `R=S`. Such containment is
forbidden by the antichain property, since `H` is nonempty and the actual
large member then strictly contains the small member. Thus cross-event
disjointness is compatible with the antichain hypothesis; it does not rescue
the unavoidable same-side intersections.

We have proved `a <= 1` and `b <= 1`, hence `m <= 2`, contradicting `m=8`.
Thus equality in (6) is impossible and the integral bound strengthens to

```text
m >= 9.                                                       (9)
```

This proves the proposed `A_3` bound under the conditional hypotheses.

## Boundary-case audit

| Case | Resolution | Label |
|---|---|---|
| `R=empty` | It is in every large down-set `D_L`; Lemma 1 also covers it when the large side is empty by forcing a suitable small event. | `PROVED` |
| `R=C` | It is in every small up-set `U_S`; Lemma 1 also covers it when the small side is empty by forcing a suitable large event. | `PROVED` |
| `R` equals a small member | `T_R=R union P` is still external, and that member itself witnesses `S subseteq R`. | `PROVED` |
| `R=L \ H` for a large member | `T_R` is still external, and that member itself witnesses `R subseteq L`. | `PROVED` |
| Small side empty | At `R=C`, Lemma 1 would force a large member containing both `C` and `H`, namely `X`, contrary to `|X \ L|>=6-i>=2`. Thus this side-empty case is inconsistent with the full internal hypotheses. Equations (3)--(6) also remain valid with `a=0`. | `PROVED` |
| Large side empty | At `R=empty`, Lemma 1 would force the small member `empty`, contrary to `|S|>=i>=2`. Thus this side-empty case is inconsistent with the full internal hypotheses. Equations (3)--(6) also remain valid with `b=0`. | `PROVED` |
| Both sides empty | Lemma 1 would read `N_p(R)=0>=1`, so an empty family cannot satisfy saturation. | `PROVED` |
| Empty set is a layer member | The internal size assumptions `|S|>=i>=2` exclude a small empty member. The coverage lemma itself does not rely on this exclusion. | `PROVED` |
| Full set is a layer member | The assumptions `|X \ L|>=6-i>=2` exclude a large full-set member for `i=2,3,4`. | `PROVED` |
| Empty core `C` | Lemma 1 still applies to its sole subset `R=empty`; the internal size conditions then make the stated hypotheses inconsistent, so the theorem is vacuous rather than exceptional. | `PROVED` |
| Strict versus non-strict containment | Saturation is used strictly on the external set `T_R`; the projected events in (1) are correctly non-strict and include member-self witnesses. | `PROVED` |
| Integer rounding | The only roundings are `m>6` to `m>=7` and `m>8` to `m>=9`, after the equality case is excluded. All preceding comparisons are rational. | `PROVED` |

## Counterexample search and hypothesis necessity

The first risky shortcut is to omit the source hypothesis `|H|>=2` and try to
use `R` itself as the saturation test. The following minimum-ground example
refutes that weakened middle-layer statement.

Let

```text
X = {h,1,2,3}, H = {h}, C = {1,2,3},
A = {C, H}.
```

The two members are incomparable. The family is saturated: every set not
containing `h` is a subset of `C`, and every set containing `h` contains `H`.
Relative to the singleton all-or-none block `H`, the member `C` is small and
the member `H` is large. They satisfy the `i=3` size restrictions

```text
|C|=3 and |X \ H|=3,
```

but the family has only two members. Oriented coverage fails, for example at
`R={1}`: neither `C subseteq R` nor `R subseteq H` holds. A nonempty proper
`P subset H` does not exist. Ground size four is minimal for this weakened
`i=3` setup because a small member already has to contain three points
outside `H`.

- `REFUTED`: the conditional theorem becomes false if the homogeneous-block
  threshold is weakened to a singleton all-or-none block.
- `PROVED`: this is not a counterexample to the theorem above or to the frozen
  Martin--Veldt definition, both of which require `|H|>=2`.

No counterexample survives all hypotheses of the conditional theorem; the
argument above resolves them symbolically for every finite `X`.

## Dependency ledger

1. `DEFINITION`: `X` is finite and `A` is a saturated antichain in `2^X`.
2. `DEFINITION`: `H` has at least two elements and every member of `A` is
   disjoint from `H` or contains all of `H`.
3. `LITERATURE` input from the frozen pack: for an intended canonical layer
   `A_i`, small members have size at least `i` and large members have
   complement size at least `6-i`.
4. `PROVED` here: dependencies 1--2 imply the pointwise oriented coverage
   lemma.
5. `PROVED` here: dependencies 3--4 and exact Bernoulli arithmetic imply the
   `7,9,7` conditional layer bounds.

`FIRST_UNCERTAIN_STEP: NONE_WITHIN_THE_CONDITIONAL_THEOREM`

`OUT_OF_SCOPE_DEPENDENCY`: verifying that the globally relevant canonical
layers exist, are saturated antichains, share the required homogeneous atom,
and inherit the exact size restrictions is deliberately not attempted here.
