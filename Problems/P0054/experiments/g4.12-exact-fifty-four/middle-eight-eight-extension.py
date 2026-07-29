#!/usr/bin/env python3
"""Test all extensions of the five-row kernels in the G4.12 (8,8) split."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections.abc import Iterator
from pathlib import Path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def minimize(rows: set[frozenset[int]]) -> tuple[frozenset[int], ...]:
    result: list[frozenset[int]] = []
    for row in sorted(rows, key=lambda current: (len(current), tuple(sorted(current)))):
        if not any(previous <= row for previous in result):
            result.append(row)
    return tuple(result)


def blockers(rows: tuple[frozenset[int], ...]) -> tuple[frozenset[int], ...]:
    candidates: tuple[frozenset[int], ...] = (frozenset(),)
    for row in rows:
        expanded: set[frozenset[int]] = set()
        for candidate in candidates:
            if candidate & row:
                expanded.add(candidate)
            else:
                expanded.update(candidate | {point} for point in row)
        candidates = minimize(expanded)
    return candidates


def is_clutter(rows: tuple[frozenset[int], ...]) -> bool:
    return all(
        left == right or not rows[left] <= rows[right]
        for left in range(len(rows))
        for right in range(len(rows))
    )


def point_degrees(rows: tuple[frozenset[int], ...]) -> dict[int, int]:
    points = frozenset().union(*rows)
    return {point: sum(point in row for row in rows) for point in points}


def parse_text_classes(path: Path) -> tuple[str, ...]:
    return tuple(
        line.split("=", 1)[1].split("|", 1)[0]
        for line in path.read_text(encoding="ascii").splitlines()
        if line.startswith("class_")
    )


def parse_json_classes(path: Path) -> tuple[str, ...]:
    payload = json.loads(path.read_text(encoding="ascii"))
    classes = payload.get("classes")
    if not isinstance(classes, list) or not all(isinstance(key, str) for key in classes):
        raise TypeError("invalid JSON kernel classes")
    return tuple(classes)


def kernel_from_key(
    key: str, row_count: int
) -> tuple[tuple[frozenset[int], ...], int]:
    supports = []
    support_key = key.split("|", 1)[0]
    for item in support_key.rstrip(",").split(","):
        support, value = item.split(":")
        supports.extend([int(support)] * int(value))
    rows = tuple(
        frozenset(
            point for point, support in enumerate(supports) if support & (1 << row)
        )
        for row in range(row_count)
    )
    return rows, len(supports)


def valid_extension(
    base: tuple[frozenset[int], ...],
    extras: tuple[frozenset[int], ...],
    kernel: tuple[frozenset[int], ...],
    x: int,
) -> bool:
    rows = base + extras
    if len(rows) != 8 or not is_clutter(rows):
        return False
    if any(len(row) < 3 or len(row) > 8 for row in rows):
        return False
    if max(point_degrees(rows).values()) > 3:
        return False
    dual = blockers(rows)
    if len(dual) != 8 or not all(row in dual for row in kernel):
        return False
    if any(len(row) < 3 or len(row) > 8 for row in dual):
        return False
    if max(point_degrees(dual).values()) > 3:
        return False
    return sum(x in row for row in dual) == 3


def single_row_candidates(
    base: tuple[frozenset[int], ...],
    x: int,
    max_degree: int,
    max_row_size: int,
    allow_x: bool,
) -> Iterator[tuple[frozenset[int], ...]]:
    degrees = point_degrees(base)
    existing = range(x + int(allow_x))
    eligible = tuple(
        point for point in existing if degrees.get(point, 0) < max_degree
    )
    for size in range(len(eligible) + 1):
        for chosen in itertools.combinations(eligible, size):
            for fresh in range(max_row_size + 1 - size):
                if not 3 <= size + fresh <= max_row_size:
                    continue
                row = frozenset(chosen) | frozenset(
                    range(x + 1, x + 1 + fresh)
                )
                yield (row,)


def two_extra_candidates(
    base: tuple[frozenset[int], ...],
    x: int,
    max_degree: int,
    max_row_size: int,
    allow_x: bool,
) -> Iterator[tuple[frozenset[int], ...]]:
    degrees = point_degrees(base)
    existing = tuple(range(x + int(allow_x)))
    for patterns in itertools.product(range(4), repeat=len(existing)):
        if any(
            degrees.get(point, 0) + bool(pattern & 1) + bool(pattern & 2) > max_degree
            for point, pattern in zip(existing, patterns, strict=True)
        ):
            continue
        first = frozenset(
            point
            for point, pattern in zip(existing, patterns, strict=True)
            if pattern & 1
        )
        second = frozenset(
            point
            for point, pattern in zip(existing, patterns, strict=True)
            if pattern & 2
        )
        for first_private in range(max_row_size + 1 - len(first)):
            for second_private in range(max_row_size + 1 - len(second)):
                for shared in range(
                    min(
                        max_row_size - len(first) - first_private,
                        max_row_size - len(second) - second_private,
                    )
                    + 1
                ):
                    if not 3 <= len(first) + first_private + shared <= max_row_size:
                        continue
                    if not 3 <= len(second) + second_private + shared <= max_row_size:
                        continue
                    next_point = x + 1
                    first_fresh = frozenset(
                        range(next_point, next_point + first_private)
                    )
                    next_point += first_private
                    second_fresh = frozenset(
                        range(next_point, next_point + second_private)
                    )
                    next_point += second_private
                    common_fresh = frozenset(range(next_point, next_point + shared))
                    rows = (
                        first | first_fresh | common_fresh,
                        second | second_fresh | common_fresh,
                    )
                    if tuple(sorted(rows, key=lambda row: tuple(sorted(row)))) != rows:
                        continue
                    yield rows


def check_class(key: str) -> dict[str, int | str]:
    kernel, old_points = kernel_from_key(key, 5)
    kernel_blockers = blockers(kernel)
    x = old_points
    pair_blockers = tuple(row for row in kernel_blockers if len(row) == 2)
    if len(pair_blockers) != 3:
        raise AssertionError("expected three pair blockers")
    base = tuple(
        row | {x} if len(row) == 2 else row for row in kernel_blockers
    )
    extras_needed = 8 - len(base)
    if extras_needed == 0:
        candidates: Iterator[tuple[frozenset[int], ...]] = iter(((),))
    elif extras_needed == 1:
        candidates = single_row_candidates(base, x, 3, 8, False)
    elif extras_needed == 2:
        candidates = two_extra_candidates(base, x, 3, 8, False)
    else:
        raise AssertionError("unexpected kernel blocker count")
    candidate_count = 0
    valid = 0
    for extras in candidates:
        candidate_count += 1
        valid += valid_extension(base, extras, kernel, x)
    return {
        "kernel": key,
        "points": old_points,
        "kernel_blockers": len(kernel_blockers),
        "pair_blockers": len(pair_blockers),
        "extra_rows": extras_needed,
        "extension_candidates": candidate_count,
        "valid_extensions": valid,
    }


def valid_degree_four_extension(
    rows: tuple[frozenset[int], ...],
    kernel: tuple[frozenset[int], ...],
    x: int,
) -> bool:
    if len(rows) != 8 or not is_clutter(rows):
        return False
    if any(len(row) < 3 or len(row) > 8 for row in rows):
        return False
    if max(point_degrees(rows).values()) > 4:
        return False
    dual = blockers(rows)
    if len(dual) != 8 or not all(row in dual for row in kernel):
        return False
    if any(len(row) < 3 or len(row) > 8 for row in dual):
        return False
    if max(point_degrees(dual).values()) > 4:
        return False
    return sum(x in row for row in dual) == 4


def check_degree_four_class(key: str) -> dict[str, int | str]:
    kernel, old_points = kernel_from_key(key, 4)
    kernel_blockers = blockers(kernel)
    x = old_points
    pair_blockers = tuple(row for row in kernel_blockers if len(row) == 2)
    other_blockers = tuple(row for row in kernel_blockers if len(row) != 2)
    if len(pair_blockers) not in (3, 4):
        raise AssertionError("unexpected four-row pair-blocker count")

    added_options: tuple[tuple[int, ...], ...]
    if len(pair_blockers) == 4:
        added_options = ((),)
    else:
        added_options = ((),) + tuple((index,) for index in range(len(other_blockers)))

    candidate_count = 0
    valid = 0
    for added in added_options:
        base = tuple(row | {x} for row in pair_blockers) + tuple(
            row | {x} if index in added else row
            for index, row in enumerate(other_blockers)
        )
        if len(base) == 8:
            candidates: Iterator[tuple[frozenset[int], ...]] = iter(((),))
        elif len(base) == 7:
            candidates = single_row_candidates(base, x, 4, 8, True)
        else:
            raise AssertionError("unexpected four-row blocker count")
        for extras in candidates:
            rows = base + extras
            if not is_clutter(rows):
                continue
            candidate_count += 1
            valid += valid_degree_four_extension(rows, kernel, x)
    return {
        "kernel": key,
        "points": old_points,
        "kernel_blockers": len(kernel_blockers),
        "pair_blockers": len(pair_blockers),
        "extension_candidates": candidate_count,
        "valid_extensions": valid,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--four-row-kernels", type=Path, required=True)
    parser.add_argument("--five-row-kernels", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    four_row_classes = parse_json_classes(args.four_row_kernels)
    five_row_classes = parse_text_classes(args.five_row_kernels)
    degree_four_results = [check_degree_four_class(key) for key in four_row_classes]
    degree_three_results = [check_class(key) for key in five_row_classes]
    report = {
        "schema": "p0054.g4.12.middle-eight-eight-extension.v1",
        "epistemic_label": "COMPUTED",
        "four_row_kernel_path": str(args.four_row_kernels),
        "four_row_kernel_sha256": sha256_file(args.four_row_kernels),
        "five_row_kernel_path": str(args.five_row_kernels),
        "five_row_kernel_sha256": sha256_file(args.five_row_kernels),
        "python_source_sha256": sha256_file(Path(__file__)),
        "degree_four": {
            "kernel_classes": len(four_row_classes),
            "extension_candidates": sum(
                int(row["extension_candidates"]) for row in degree_four_results
            ),
            "valid_extensions": sum(
                int(row["valid_extensions"]) for row in degree_four_results
            ),
            "classes": degree_four_results,
        },
        "degree_three": {
            "kernel_classes": len(five_row_classes),
            "extension_candidates": sum(
                int(row["extension_candidates"]) for row in degree_three_results
            ),
            "valid_extensions": sum(
                int(row["valid_extensions"]) for row in degree_three_results
            ),
            "classes": degree_three_results,
        },
    }
    args.output.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="ascii"
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
