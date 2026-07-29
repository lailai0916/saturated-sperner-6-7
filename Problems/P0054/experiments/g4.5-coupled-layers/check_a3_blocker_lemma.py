#!/usr/bin/env python3
"""Finite exact checks for the proposed A3 blocker obstruction.

The theorem in the companion proof is arbitrary-finite; this program is only
regression evidence.  It enumerates labelled clutters with three or four rows
on small ground sets, computes blockers in two independent ways, and checks
the hypotheses tau >= 3 and row size >= 3.
"""

from __future__ import annotations

import itertools
import json
from collections import Counter

Family = tuple[frozenset[int], ...]


def subsets(n: int, minimum: int = 0) -> tuple[frozenset[int], ...]:
    return tuple(
        frozenset(i for i in range(n) if mask & (1 << i))
        for mask in range(1 << n)
        if mask.bit_count() >= minimum
    )


def is_clutter(family: Family) -> bool:
    return all(
        left == right or not (left <= right or right <= left)
        for left, right in itertools.combinations(family, 2)
    )


def blocker_powerset(family: Family, n: int) -> Family:
    hitting = tuple(
        frozenset(i for i in range(n) if mask & (1 << i))
        for mask in range(1 << n)
        if all(mask & sum(1 << i for i in edge) for edge in family)
    )
    return tuple(
        candidate
        for candidate in hitting
        if not any(other < candidate for other in hitting)
    )


def blocker_choices(family: Family) -> Family:
    choices = {frozenset(choice) for choice in itertools.product(*family)}
    ordered = sorted(choices, key=lambda edge: (len(edge), tuple(sorted(edge))))
    minimal: list[frozenset[int]] = []
    for candidate in ordered:
        if not any(old <= candidate for old in minimal):
            minimal.append(candidate)
    return tuple(minimal)


def normalize(family: Family) -> tuple[tuple[int, ...], ...]:
    return tuple(sorted(tuple(sorted(edge)) for edge in family))


def inspect(n: int, rows: int) -> dict[str, object]:
    candidates = subsets(n, minimum=3)
    total = 0
    clutters = 0
    tau_ge_3 = 0
    blocker_sizes: Counter[int] = Counter()
    minimum_seen: int | None = None
    for family_list in itertools.combinations(candidates, rows):
        total += 1
        family = tuple(family_list)
        if not is_clutter(family):
            continue
        clutters += 1
        blockers_a = blocker_powerset(family, n)
        blockers_b = blocker_choices(family)
        if normalize(blockers_a) != normalize(blockers_b):
            raise AssertionError((n, rows, family, blockers_a, blockers_b))
        if not blockers_a or min(map(len, blockers_a)) < 3:
            continue
        tau_ge_3 += 1
        blocker_size = len(blockers_a)
        blocker_sizes[blocker_size] += 1
        minimum_seen = (
            blocker_size
            if minimum_seen is None
            else min(minimum_seen, blocker_size)
        )
        if rows == 3 and blocker_size < 27:
            raise AssertionError(("three-row bound", n, family, blockers_a))
        if rows == 4 and blocker_size < 6:
            raise AssertionError(("four-row bound", n, family, blockers_a))
        # The second implementation is also checked after dualization.
        if normalize(blocker_powerset(blockers_a, n)) != normalize(family):
            raise AssertionError(("involution", n, rows, family))
    return {
        "ground_size": n,
        "rows": rows,
        "candidate_row_families": total,
        "clutters": clutters,
        "tau_at_least_3": tau_ge_3,
        "blocker_size_histogram": dict(sorted(blocker_sizes.items())),
        "minimum_blocker_count_seen": minimum_seen,
    }


def named_examples() -> list[dict[str, object]]:
    """Check non-vacuous star, triangle-plus-isolate, and disjoint examples."""

    examples = [
        (
            "three_disjoint_rows",
            9,
            (
                frozenset((0, 1, 2)),
                frozenset((3, 4, 5)),
                frozenset((6, 7, 8)),
            ),
            27,
        ),
        (
            "four_star_no_center_exclusive",
            9,
            (
                frozenset((0, 1, 2)),
                frozenset((3, 4, 5)),
                frozenset((6, 7, 8)),
                frozenset((0, 3, 6)),
            ),
            19,
        ),
        (
            "four_triangle_plus_isolate",
            8,
            (
                frozenset((0, 1, 2)),
                frozenset((0, 3, 4)),
                frozenset((1, 3, 4)),
                frozenset((5, 6, 7)),
            ),
            21,
        ),
    ]
    records: list[dict[str, object]] = []
    for name, n, family, expected in examples:
        blockers_a = blocker_powerset(family, n)
        blockers_b = blocker_choices(family)
        if normalize(blockers_a) != normalize(blockers_b):
            raise AssertionError(("named validator disagreement", name))
        if len(blockers_a) != expected or min(map(len, blockers_a)) < 3:
            raise AssertionError(("named bound", name, len(blockers_a)))
        records.append(
            {
                "name": name,
                "ground_size": n,
                "rows": len(family),
                "blocker_count": len(blockers_a),
                "blocker_minimum_size": min(map(len, blockers_a)),
            }
        )
    return records


def main() -> None:
    records = [inspect(n, rows) for n in range(3, 7) for rows in (3, 4)]
    result = {
        "epistemic_label": "COMPUTED",
        "named_examples": named_examples(),
        "scope": "labelled clutters on ground sizes 3..6 only",
        "theorem_not_inferred": True,
        "records": records,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
