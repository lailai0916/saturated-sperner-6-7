# Exact oriented reduction for the eight-core size-54 search

## Scope

Fix an eight-element core `C`, a disjoint nonempty block `H`, and seven layers
whose members are templates `A` or `A ∪ H`, with `A ⊆ C`.  This note concerns
only the complete common-block layered template class in `statement.md`.  It
does not cover arbitrary saturated 7-Sperner systems.

## Proposition 1 — one oriented coverage condition is exact

For one layer, write `S` for the selected small core sets and `L` for the core
sets of the selected large templates.  Assume the selected templates form an
antichain.  The layer is saturated in `P(C ∪ H)` if and only if, for every
`R ⊆ C`,

```text
there is S in S with S ⊆ R, or there is L in L with R ⊆ L.       (1)
```

### Proof

Suppose first that the layer is saturated.  Choose a nonempty proper subset
`P ⊂ H` and consider `R ∪ P`.  It is not a template and therefore is external
to the layer.  Saturation makes it strictly comparable with a selected
template.  A selected small template can be comparable with `R ∪ P` only by
lying below it, which gives `S ⊆ R`.  A selected large template can be
comparable with `R ∪ P` only by lying above it, which gives `R ⊆ L`.  Hence
(1) is necessary.

Conversely, let `T ⊆ C ∪ H` be external and put `R = T ∩ C`.  If the first
alternative of (1) holds, then `S ⊆ T`; the containment is strict because `T`
is external.  If the second alternative holds, then `T ⊆ L ∪ H`; this
containment is likewise strict because `T` is external.  Thus every external
set is strictly comparable with a layer member, proving saturation.  The
antichain assumption supplies the other half of maximal-antichain status.

The argument uses a genuine partial state of `H`; the P0054 hypothesis
`|H| > 2` is more than sufficient.

## Proposition 2 — target 54 has a representative with at most 27 small members

Complement every template in `C ∪ H` and reverse the order of the seven
layers.  Explicitly,

```text
A            maps to (C \ A) ∪ H,
A ∪ H        maps to C \ A,
layer i      maps to layer 6-i.
```

This involution preserves antichains, saturation, pairwise disjointness,
strict containment after layer reversal, and total cardinality.  It exchanges
the total numbers of small and large templates.  Therefore, for every
candidate of total size at most 54, either the candidate or its dual contains
at most 27 small templates.

Consequently the constraint

```text
total selected small templates <= 27
```

is a safe symmetry breaker for deciding whether a target-54 candidate exists.
It is not valid as an asymmetric claim about every candidate; it is valid
because at least one member of each dual pair satisfies it.

## CNF encoding

The oriented CNF keeps one variable for each `(layer, small/large, core mask)`.
For each layer it contains:

1. the exact antichain exclusions among small, among large, and across small
   and large templates;
2. one clause (1) for each of the 256 core masks;
3. the exact predecessor clauses for layering;
4. pairwise layer-disjointness clauses;
5. a self-contained sequential counter for total size at most 54; and
6. a second sequential counter for at most 27 small templates.

The resulting eight-core file has 3,584 primary variables, 241,839 auxiliary
variables, and 638,705 clauses.  Its SHA-256 digest is
`975d47af99af174850301de76dbe89bdab488b1cb31372417c5a9dce9cf1d078`.

The equivalence in Proposition 1 was also checked exhaustively for all 256
possible selections of templates over a two-element core.  This finite check
is regression evidence; the general result is the proof above.

## Evidence boundary

The reduction is `PROVED`.  The solver runs made with it are only `COMPUTED`.
No solver returned SAT or a checkable UNSAT certificate within the recorded
limits.  Therefore this work neither constructs 54 members nor proves that 54
is impossible.
