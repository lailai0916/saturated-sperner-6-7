# P0054 G4.2 frozen subproblem

## Exact layer statement

`CONJECTURED` (`THEOREM_A2_CANDIDATE`): in the G4 global minimum-family and
canonical-decomposition setting, every second internal layer satisfies

\[
|A_2|\ge 8.
\]

The ground-set remainder `U` is an arbitrary finite set. A hypothetical
seven-member layer has `a` small members and `b` large members, with
`a+b=7`. Every small generator `S` has `|S|>=2`. For every large trace `K`,
its complement `C=U\setminus K` has `|C|>=4`. The layer is an antichain, so
`S` is not contained in any `K`, equivalently `S` meets every `C`.

For every `R subseteq U`, oriented saturation gives

\[
\sum_S 1[S\subseteq R]+\sum_K1[R\subseteq K]\ge1.
\]

Equivalently, a counterexample to coverage is a set `R` which meets every
large complement `C` but contains no complete small generator `S`.

## Required evidence discipline

- Probability comparisons use exact rational arithmetic only.
- Finite searches are `COMPUTED` unless an external certificate and a proved
  arbitrary-`U` reduction are both present.
- Repetitions of incidence patterns, nonuniform set sizes, empty sides,
  duplicate-looking traces, and arbitrarily large finite `U` must be audited.
- No G0--G4 file, P0054-C1--C17, Lean file, certificate, or manifest may be
  modified.
- No network, Formalizer, stage, commit, push, publication, or size-54 CNF
  rerun is permitted.
