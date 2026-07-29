#!/usr/bin/env python3
"""Exact loop-multigraph support checks for P0054 G4.10."""

from __future__ import annotations

import argparse
import json
from itertools import combinations
from pathlib import Path


def support_data(n: int) -> tuple[tuple[tuple[int, ...], ...], tuple[int, ...]]:
    vertices = tuple(range(n))
    supports = tuple((v,) for v in vertices) + tuple(combinations(vertices, 2))
    masks = tuple(sum(1 << v for v in support) for support in supports)
    return supports, masks


def minimal_support_covers(n: int, masks: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    full = (1 << n) - 1
    covers = []
    for size in range(1, n + 1):
        for indices in combinations(range(len(masks)), size):
            union = 0
            for index in indices:
                union |= masks[index]
            if union != full:
                continue
            if all(
                any(
                    masks[index] & (1 << vertex)
                    for vertex in range(n)
                    if all(
                        other == index or not masks[other] & (1 << vertex)
                        for other in indices
                    )
                )
                for index in indices
            ):
                covers.append(indices)
    return tuple(covers)


def enumerate_branch(
    n: int,
    low_count: int,
    supports: tuple[tuple[int, ...], ...],
    covers: tuple[tuple[int, ...], ...],
    require_perfect_matching: bool,
) -> tuple[int, int, tuple[int, ...]]:
    low = frozenset(range(low_count))
    high = frozenset(range(low_count, n))
    allowed = tuple(
        index
        for index, support in enumerate(supports)
        if any(vertex in low for vertex in support)
    )
    degrees = [0] * n
    multiplicities = [0] * len(supports)
    valid = 0
    minimum: int | None = None
    minimizer: tuple[int, ...] | None = None

    def visit(position: int) -> None:
        nonlocal valid, minimum, minimizer
        if position == len(allowed):
            if any(degrees[vertex] != 3 for vertex in low):
                return
            if any(degrees[vertex] < 4 for vertex in high):
                return
            total = 0
            has_perfect_matching = False
            for cover in covers:
                choices = 1
                for index in cover:
                    choices *= multiplicities[index]
                    if choices == 0:
                        break
                total += choices
                if choices and len(cover) == n // 2:
                    has_perfect_matching = True
            if require_perfect_matching and not has_perfect_matching:
                return
            valid += 1
            if minimum is None or total < minimum:
                minimum = total
                minimizer = tuple(multiplicities)
            return

        index = allowed[position]
        support = supports[index]
        low_endpoints = tuple(vertex for vertex in support if vertex in low)
        capacity = min(3 - degrees[vertex] for vertex in low_endpoints)
        for value in range(capacity + 1):
            multiplicities[index] = value
            for vertex in support:
                degrees[vertex] += value
            visit(position + 1)
            for vertex in support:
                degrees[vertex] -= value
        multiplicities[index] = 0

    visit(0)
    if minimum is None or minimizer is None:
        raise AssertionError("empty branch")
    return valid, minimum, minimizer


def vector_terms(
    supports: tuple[tuple[int, ...], ...],
    vector: tuple[int, ...],
) -> list[str]:
    return [
        "{" + ",".join(str(vertex + 1) for vertex in support) + f"}}x{value}"
        for support, value in zip(supports, vector, strict=True)
        if value
    ]


def run_case(
    n: int,
    low_counts: tuple[int, ...],
    expected_cover_histogram: dict[int, int],
    expected_branches: dict[int, tuple[int, int]],
    require_perfect_matching: bool,
) -> dict[str, object]:
    supports, masks = support_data(n)
    covers = minimal_support_covers(n, masks)
    histogram = {
        size: sum(len(cover) == size for cover in covers)
        for size in range(1, n + 1)
    }
    if histogram != expected_cover_histogram:
        raise AssertionError((histogram, expected_cover_histogram))

    branches = []
    for low_count in low_counts:
        valid, minimum, minimizer = enumerate_branch(
            n,
            low_count,
            supports,
            covers,
            require_perfect_matching,
        )
        if (valid, minimum) != expected_branches[low_count]:
            raise AssertionError(((valid, minimum), expected_branches[low_count]))
        branches.append(
            {
                "low_count": low_count,
                "vectors": valid,
                "minimum_blockers": minimum,
                "minimizer": vector_terms(supports, minimizer),
            }
        )
    return {
        "vertices": n,
        "supports": len(supports),
        "minimal_support_covers": len(covers),
        "cover_size_histogram": histogram,
        "branches": branches,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    split_59 = run_case(
        n=5,
        low_counts=(3, 4, 5),
        expected_cover_histogram={1: 0, 2: 0, 3: 45, 4: 65, 5: 1},
        expected_branches={3: (54, 19), 4: (2445, 16), 5: (2698, 15)},
        require_perfect_matching=False,
    )
    split_68 = run_case(
        n=6,
        low_counts=(4, 5, 6),
        expected_cover_histogram={1: 0, 2: 0, 3: 15, 4: 375, 5: 171, 6: 1},
        expected_branches={4: (2601, 24), 5: (31772, 21), 6: (27325, 15)},
        require_perfect_matching=True,
    )
    payload = {
        "label": "COMPUTED",
        "scope": "complete support-multiplicity kernels for G4.10 splits (5,9) and (6,8)",
        "split_5_9": split_59,
        "split_6_8": split_68,
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
