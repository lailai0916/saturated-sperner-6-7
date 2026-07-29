#!/usr/bin/env python3
"""Test the four-row extensions in the G4.12 (7,9) split."""

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


def parse_classes(path: Path) -> tuple[str, ...]:
    payload = json.loads(path.read_text(encoding="ascii"))
    classes = payload.get("classes")
    if not isinstance(classes, list) or not all(isinstance(key, str) for key in classes):
        raise TypeError("invalid JSON kernel classes")
    return tuple(classes)


def kernel_from_key(key: str) -> tuple[tuple[frozenset[int], ...], int]:
    supports = []
    support_key = key.split("|", 1)[0]
    for item in support_key.rstrip(",").split(","):
        support, value = item.split(":")
        supports.extend([int(support)] * int(value))
    rows = tuple(
        frozenset(point for point, support in enumerate(supports) if support & (1 << row))
        for row in range(4)
    )
    return rows, len(supports)


def single_row_candidates(
    base: tuple[frozenset[int], ...],
    x: int,
) -> Iterator[tuple[frozenset[int], ...]]:
    degrees = point_degrees(base)
    eligible = tuple(point for point in range(x + 1) if degrees.get(point, 0) < 4)
    for size in range(len(eligible) + 1):
        for chosen in itertools.combinations(eligible, size):
            for fresh in range(8 - size):
                if not 3 <= size + fresh <= 7:
                    continue
                row = frozenset(chosen) | frozenset(range(x + 1, x + 1 + fresh))
                yield (row,)


def two_row_candidates(
    base: tuple[frozenset[int], ...],
    x: int,
) -> Iterator[tuple[frozenset[int], ...]]:
    degrees = point_degrees(base)
    existing = tuple(range(x + 1))
    for patterns in itertools.product(range(4), repeat=len(existing)):
        if any(
            degrees.get(point, 0) + bool(pattern & 1) + bool(pattern & 2) > 4
            for point, pattern in zip(existing, patterns, strict=True)
        ):
            continue
        first = frozenset(
            point for point, pattern in zip(existing, patterns, strict=True) if pattern & 1
        )
        second = frozenset(
            point for point, pattern in zip(existing, patterns, strict=True) if pattern & 2
        )
        for first_private in range(8 - len(first)):
            for second_private in range(8 - len(second)):
                max_shared = min(
                    7 - len(first) - first_private,
                    7 - len(second) - second_private,
                )
                for shared in range(max_shared + 1):
                    if not 3 <= len(first) + first_private + shared <= 7:
                        continue
                    if not 3 <= len(second) + second_private + shared <= 7:
                        continue
                    next_point = x + 1
                    first_fresh = frozenset(range(next_point, next_point + first_private))
                    next_point += first_private
                    second_fresh = frozenset(range(next_point, next_point + second_private))
                    next_point += second_private
                    common_fresh = frozenset(range(next_point, next_point + shared))
                    rows = (
                        first | first_fresh | common_fresh,
                        second | second_fresh | common_fresh,
                    )
                    if tuple(sorted(rows, key=lambda row: tuple(sorted(row)))) != rows:
                        continue
                    yield rows


def valid_extension(
    rows: tuple[frozenset[int], ...],
    kernel: tuple[frozenset[int], ...],
    x: int,
) -> bool:
    if len(rows) != 9 or not is_clutter(rows):
        return False
    if any(not 3 <= len(row) <= 7 for row in rows):
        return False
    if max(point_degrees(rows).values()) > 4:
        return False
    dual = blockers(rows)
    if len(dual) != 7 or not all(row in dual for row in kernel):
        return False
    if any(not 3 <= len(row) <= 9 for row in dual):
        return False
    if max(point_degrees(dual).values()) > 3:
        return False
    return sum(x in row for row in dual) == 3


def check_class(key: str) -> dict[str, int | str]:
    kernel, old_points = kernel_from_key(key)
    kernel_blockers = blockers(kernel)
    x = old_points
    pair_blockers = tuple(row for row in kernel_blockers if len(row) == 2)
    other_blockers = tuple(row for row in kernel_blockers if len(row) != 2)
    if len(pair_blockers) not in (3, 4):
        raise AssertionError("unexpected pair-blocker count")

    optional_count = 4 - len(pair_blockers)
    added_options = tuple(
        added
        for size in range(optional_count + 1)
        for added in itertools.combinations(range(len(other_blockers)), size)
    )
    candidate_count = 0
    valid = 0
    for added in added_options:
        base = tuple(row | {x} for row in pair_blockers) + tuple(
            row | {x} if index in added else row for index, row in enumerate(other_blockers)
        )
        extras_needed = 9 - len(base)
        if extras_needed == 0:
            candidates: Iterator[tuple[frozenset[int], ...]] = iter(((),))
        elif extras_needed == 1:
            candidates = single_row_candidates(base, x)
        elif extras_needed == 2:
            candidates = two_row_candidates(base, x)
        else:
            raise AssertionError("unexpected kernel blocker count")
        for extras in candidates:
            rows = base + extras
            if not is_clutter(rows):
                continue
            candidate_count += 1
            valid += valid_extension(rows, kernel, x)
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
    parser.add_argument("--kernels", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    results = [check_class(key) for key in parse_classes(args.kernels)]
    report = {
        "schema": "p0054.g4.12.middle-seven-nine-extension.v1",
        "epistemic_label": "COMPUTED",
        "kernel_path": str(args.kernels),
        "kernel_sha256": sha256_file(args.kernels),
        "python_source_sha256": sha256_file(Path(__file__)),
        "kernel_classes": len(results),
        "extension_candidates": sum(int(result["extension_candidates"]) for result in results),
        "valid_extensions": sum(int(result["valid_extensions"]) for result in results),
        "classes": results,
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
