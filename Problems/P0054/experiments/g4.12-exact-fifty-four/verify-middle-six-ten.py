from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from collections import Counter
from collections.abc import Iterable
from pathlib import Path

SUPPORTS = tuple(range(1, 15))


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def minimal_support_covers() -> tuple[frozenset[int], ...]:
    result = []
    for size in range(2, 5):
        for chosen in itertools.combinations(range(14), size):
            union = 0
            for index in chosen:
                union |= SUPPORTS[index]
            if union != 15:
                continue
            if any(
                _union(SUPPORTS[index] for index in chosen if index != omitted) == 15
                for omitted in chosen
            ):
                continue
            result.append(frozenset(chosen))
    return tuple(result)


def _union(values: Iterable[int]) -> int:
    result = 0
    for value in values:
        result |= value
    return result


def is_clutter(active: tuple[int, ...]) -> bool:
    return all(
        any(
            SUPPORTS[index] & (1 << left) and not SUPPORTS[index] & (1 << right)
            for index in active
        )
        for left in range(4)
        for right in range(4)
        if left != right
    )


def weighted_profile(
    covers: tuple[frozenset[int], ...], multiplicity: tuple[int, ...]
) -> tuple[int, int]:
    total = 0
    pairs = 0
    for cover in covers:
        choices = math.prod(multiplicity[index] or 1 for index in cover)
        total += choices
        if len(cover) == 2:
            pairs += choices
    return total, pairs


def canonical_key(multiplicity: tuple[int, ...]) -> str:
    candidates = []
    for permutation in itertools.permutations(range(4)):
        transformed = []
        for index, value in enumerate(multiplicity):
            if not value:
                continue
            image = sum(
                1 << permutation[row]
                for row in range(4)
                if SUPPORTS[index] & (1 << row)
            )
            transformed.append((image, value))
        candidates.append(tuple(sorted(transformed)))
    return "".join(f"{support}:{value}," for support, value in min(candidates))


def actual_rows_and_blockers(
    covers: tuple[frozenset[int], ...], multiplicity: tuple[int, ...]
) -> tuple[tuple[frozenset[int], ...], set[frozenset[int]], int]:
    points_by_support: dict[int, tuple[int, ...]] = {}
    point_supports: list[int] = []
    for index, value in enumerate(multiplicity):
        current = tuple(range(len(point_supports), len(point_supports) + value))
        points_by_support[index] = current
        point_supports.extend([SUPPORTS[index]] * value)
    rows = tuple(
        frozenset(
            point for point, support in enumerate(point_supports) if support & (1 << row)
        )
        for row in range(4)
    )
    blockers = {
        frozenset(chosen)
        for cover in covers
        for chosen in itertools.product(*(points_by_support[index] for index in cover))
    }
    return rows, blockers, len(point_supports)


def compatible_with_kernel_a(
    covers: tuple[frozenset[int], ...], multiplicity: tuple[int, ...]
) -> bool:
    rows, blockers, point_count = actual_rows_and_blockers(covers, multiplicity)
    required = max(0, len(blockers) - 3)
    for row in rows:
        if len(row) != 3:
            continue
        for a, b, c in itertools.permutations(row):
            outside = tuple(point for point in range(point_count) if point not in row)
            for u, v, w in itertools.permutations(outside, 3):
                fixed = (
                    frozenset((a, u, v)),
                    frozenset((b, u, w)),
                    frozenset((c, v, w)),
                )
                if sum(candidate in blockers for candidate in fixed) >= required:
                    return True
    return False


def multiplicity_vectors_for_active(
    active: tuple[int, ...], covers: tuple[frozenset[int], ...]
) -> tuple[tuple[int, ...], ...]:
    result = []
    values = [0] * 14
    degrees = [0] * 4

    def visit(position: int) -> None:
        if position == len(active):
            if min(degrees) < 3 or 3 not in degrees:
                return
            multiplicity = tuple(values)
            if weighted_profile(covers, multiplicity)[0] <= 6:
                result.append(multiplicity)
            return

        index = active[position]
        support = SUPPORTS[index]
        capacity = min(6 - degrees[row] for row in range(4) if support & (1 << row))
        for value in range(1, capacity + 1):
            values[index] = value
            for row in range(4):
                if support & (1 << row):
                    degrees[row] += value
            if weighted_profile(covers, tuple(values))[0] <= 6:
                visit(position + 1)
            for row in range(4):
                if support & (1 << row):
                    degrees[row] -= value
        values[index] = 0

    visit(0)
    return tuple(result)


def enumerate_summary() -> dict[str, int | str]:
    all_covers = minimal_support_covers()
    summary: dict[str, int | str] = {
        "schema": "p0054.g4.12.middle-six-ten.v1",
        "supports": 14,
        "minimal_support_covers": len(all_covers),
        "active_masks_checked": (1 << 14) - 1,
    }
    support_feasible = 0
    vector_count = 0
    compatible_count = 0
    histogram: Counter[tuple[int, int]] = Counter()
    classes: set[str] = set()

    for active_mask in range(1, 1 << 14):
        active = tuple(index for index in range(14) if active_mask & (1 << index))
        support_degrees = tuple(
            sum(bool(SUPPORTS[index] & (1 << row)) for index in active) for row in range(4)
        )
        if min(support_degrees) == 0 or max(support_degrees) > 6 or not is_clutter(active):
            continue
        active_set = frozenset(active)
        covers = tuple(cover for cover in all_covers if cover <= active_set)
        if not covers or len(covers) > 6 or frozenset().union(*covers) != active_set:
            continue
        support_feasible += 1
        for multiplicity in multiplicity_vectors_for_active(active, covers):
            total, pairs = weighted_profile(covers, multiplicity)
            vector_count += 1
            histogram[total, pairs] += 1
            classes.add(canonical_key(multiplicity))
            if compatible_with_kernel_a(covers, multiplicity):
                compatible_count += 1

    summary["support_feasible_masks"] = support_feasible
    summary["multiplicity_vectors"] = vector_count
    for (total, pairs), frequency in sorted(histogram.items()):
        summary[f"blockers_{total}_pairs_{pairs}"] = frequency
    summary["row_permutation_classes"] = len(classes)
    for index, key in enumerate(sorted(classes), 1):
        summary[f"class_{index}"] = key
    summary["compatible_extensions"] = compatible_count
    return summary


def parse_reference(path: Path) -> dict[str, int | str]:
    result: dict[str, int | str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        key, value = line.split("=", 1)
        result[key] = value if key == "schema" or key.startswith("class_") else int(value)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    reference = parse_reference(args.reference)
    actual = enumerate_summary()
    if actual != reference:
        raise AssertionError(
            {
                "missing": sorted(set(reference) - set(actual)),
                "extra": sorted(set(actual) - set(reference)),
                "mismatched": sorted(
                    key for key in set(reference) & set(actual) if reference[key] != actual[key]
                ),
            }
        )

    source = Path(__file__).with_name("middle-six-ten.cpp")
    report = {
        "schema": "p0054.g4.12.middle-six-ten-verification.v1",
        "epistemic_label": "COMPUTED",
        "reference_path": str(args.reference),
        "reference_sha256": sha256_file(args.reference),
        "cpp_source_sha256": sha256_file(source),
        "python_source_sha256": sha256_file(Path(__file__)),
        "independent_replay_match": True,
        "summary": actual,
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
