#!/usr/bin/env python3
"""Enumerate bounded four-row kernels for the remaining G4.12 middle splits."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path

ROWS = 4
FULL = (1 << ROWS) - 1
SUPPORTS = tuple(range(1, FULL))


def minimal_support_covers() -> tuple[tuple[int, ...], ...]:
    result = []
    for size in range(2, ROWS + 1):
        for cover in itertools.combinations(range(len(SUPPORTS)), size):
            if set().union(*(set_bits(SUPPORTS[index]) for index in cover)) != set(
                range(ROWS)
            ):
                continue
            if all(
                any(
                    SUPPORTS[index] & (1 << row)
                    and all(
                        other == index or not SUPPORTS[other] & (1 << row)
                        for other in cover
                    )
                    for row in range(ROWS)
                )
                for index in cover
            ):
                result.append(cover)
    return tuple(result)


def set_bits(mask: int) -> frozenset[int]:
    return frozenset(row for row in range(ROWS) if mask & (1 << row))


COVERS = minimal_support_covers()


def is_clutter(active: tuple[int, ...]) -> bool:
    for left in range(ROWS):
        for right in range(ROWS):
            if left == right:
                continue
            if all(
                not (SUPPORTS[index] & (1 << left))
                or SUPPORTS[index] & (1 << right)
                for index in active
            ):
                return False
    return True


def weighted_counts(
    covers: tuple[tuple[int, ...], ...], multiplicity: tuple[int, ...]
) -> tuple[int, int]:
    total = 0
    pairs = 0
    for cover in covers:
        choices = 1
        for index in cover:
            choices *= multiplicity[index]
        total += choices
        if len(cover) == 2:
            pairs += choices
    return total, pairs


def canonical_key(multiplicity: tuple[int, ...], total: int, pairs: int) -> str:
    candidates = []
    for permutation in itertools.permutations(range(ROWS)):
        transformed = []
        for index, value in enumerate(multiplicity):
            if not value:
                continue
            image = sum(
                1 << permutation[row]
                for row in range(ROWS)
                if SUPPORTS[index] & (1 << row)
            )
            transformed.append((image, value))
        candidates.append(tuple(sorted(transformed)))
    support_key = ",".join(
        f"{support}:{value}" for support, value in min(candidates)
    )
    return f"{support_key}|b:{total}|p:{pairs}"


def multiplicity_data(
    active: tuple[int, ...],
    covers: tuple[tuple[int, ...], ...],
    max_row_size: int,
    max_blockers: int,
    max_pair_blockers: int,
) -> tuple[int, Counter[tuple[int, int]], set[str]]:
    vector_count = 0
    histogram: Counter[tuple[int, int]] = Counter()
    classes: set[str] = set()
    degree = [0] * ROWS
    multiplicity = [0] * len(SUPPORTS)

    def visit(position: int) -> None:
        nonlocal vector_count
        if position == len(active):
            if min(degree) < 3:
                return
            current = tuple(multiplicity)
            total, pairs = weighted_counts(covers, current)
            if total > max_blockers or pairs > max_pair_blockers:
                return
            vector_count += 1
            histogram[total, pairs] += 1
            classes.add(canonical_key(current, total, pairs))
            return

        index = active[position]
        support = SUPPORTS[index]
        capacity = min(
            max_row_size - degree[row]
            for row in range(ROWS)
            if support & (1 << row)
        )
        for value in range(1, capacity + 1):
            multiplicity[index] = value
            for row in range(ROWS):
                if support & (1 << row):
                    degree[row] += value
            total, pairs = weighted_counts(covers, tuple(multiplicity))
            if total <= max_blockers and pairs <= max_pair_blockers:
                visit(position + 1)
            for row in range(ROWS):
                if support & (1 << row):
                    degree[row] -= value
        multiplicity[index] = 0

    visit(0)
    return vector_count, histogram, classes


def enumerate_kernels(
    max_row_size: int, max_blockers: int, max_pair_blockers: int
) -> dict[str, object]:
    active_masks_checked = (1 << len(SUPPORTS)) - 1
    support_feasible_masks = 0
    multiplicity_vectors = 0
    histogram: Counter[tuple[int, int]] = Counter()
    classes: set[str] = set()

    for active_mask in range(1, 1 << len(SUPPORTS)):
        active = tuple(
            index for index in range(len(SUPPORTS)) if active_mask & (1 << index)
        )
        support_degrees = tuple(
            sum(bool(SUPPORTS[index] & (1 << row)) for index in active)
            for row in range(ROWS)
        )
        if min(support_degrees) == 0 or max(support_degrees) > max_row_size:
            continue
        if not is_clutter(active):
            continue
        active_set = frozenset(active)
        covers = tuple(cover for cover in COVERS if frozenset(cover) <= active_set)
        if not covers:
            continue
        if len(covers) > max_blockers:
            continue
        if sum(len(cover) == 2 for cover in covers) > max_pair_blockers:
            continue
        if frozenset().union(*(frozenset(cover) for cover in covers)) != active_set:
            continue
        support_feasible_masks += 1
        vector_count, current_histogram, current_classes = multiplicity_data(
            active,
            covers,
            max_row_size,
            max_blockers,
            max_pair_blockers,
        )
        multiplicity_vectors += vector_count
        histogram.update(current_histogram)
        classes.update(current_classes)

    return {
        "schema": "p0054.g4.12.middle-four-row-kernels.v1",
        "epistemic_label": "COMPUTED",
        "parameters": {
            "max_row_size": max_row_size,
            "max_blockers": max_blockers,
            "max_pair_blockers": max_pair_blockers,
        },
        "supports": len(SUPPORTS),
        "minimal_support_covers": len(COVERS),
        "active_masks_checked": active_masks_checked,
        "support_feasible_masks": support_feasible_masks,
        "multiplicity_vectors": multiplicity_vectors,
        "blocker_histogram": {
            f"blockers_{total}_pairs_{pairs}": count
            for (total, pairs), count in sorted(histogram.items())
        },
        "row_permutation_classes": len(classes),
        "classes": sorted(classes),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-row-size", type=int, required=True)
    parser.add_argument("--max-blockers", type=int, required=True)
    parser.add_argument("--max-pair-blockers", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    result = enumerate_kernels(
        args.max_row_size, args.max_blockers, args.max_pair_blockers
    )
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="ascii"
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
