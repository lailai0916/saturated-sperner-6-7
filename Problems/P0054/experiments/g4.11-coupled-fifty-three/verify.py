"""Independent semantic checks for the P0054 G4.11 kernel outputs."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def minimalize(values: list[int]) -> list[int]:
    result: list[int] = []
    for value in sorted(set(values), key=lambda item: (item.bit_count(), item)):
        if not any(old & value == old for old in result):
            result.append(value)
    return result


def blockers(rows: list[int]) -> list[int]:
    covers = [0]
    for row in rows:
        expanded: list[int] = []
        for cover in covers:
            if cover & row:
                expanded.append(cover)
            else:
                for point in range(row.bit_length()):
                    bit = 1 << point
                    if row & bit:
                        expanded.append(cover | bit)
        covers = minimalize(expanded)
    return sorted(covers, key=lambda item: (item.bit_count(), item))


def is_clutter(rows: list[int]) -> bool:
    return all(
        left & right != left
        for index, left in enumerate(rows)
        for other_index, right in enumerate(rows)
        if index != other_index
    )


def degrees(rows: list[int], point_count: int) -> list[int]:
    return [sum(bool(row & (1 << point)) for row in rows) for point in range(point_count)]


def parse_term(term: str) -> tuple[int, int]:
    support, count = term.split(":")
    return int(support), int(count)


def parse_classes(path: Path) -> list[list[tuple[int, int]]]:
    classes: list[list[tuple[int, int]]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("class="):
            continue
        key = line.removeprefix("class=").split("|", 1)[0]
        classes.append(
            [parse_term(term) for term in key.split(",") if term]
        )
    return classes


def rows_from_class(data: list[tuple[int, int]], row_count: int) -> tuple[list[int], int]:
    supports = [support for support, count in data for _ in range(count)]
    rows = [0] * row_count
    for point, support in enumerate(supports):
        for row in range(row_count):
            if support & (1 << row):
                rows[row] |= 1 << point
    return rows, len(supports)


def valid_extension(c: list[int], kernel: list[int], point_count: int, x: int) -> bool:
    if len(c) != 7 or not is_clutter(c) or max(degrees(c, point_count)) > 3:
        return False
    if any(not 3 <= row.bit_count() <= 8 for row in c):
        return False
    d = blockers(c)
    if len(d) != 8 or not set(kernel) <= set(d):
        return False
    if max(degrees(d, point_count)) > 3:
        return False
    if any(not 3 <= row.bit_count() <= 7 for row in d):
        return False
    return sum(bool(row & (1 << x)) for row in d) == 3


def check_five_row_classes(classes: list[list[tuple[int, int]]]) -> dict[str, object]:
    if len(classes) != 8:
        raise AssertionError(f"expected 8 classes, found {len(classes)}")
    blocker_distribution: dict[str, int] = {}
    total_q_candidates = 0
    valid_extensions = 0
    class_records: list[dict[str, int]] = []
    for data in classes:
        kernel, old_point_count = rows_from_class(data, 5)
        if not is_clutter(kernel):
            raise AssertionError("saved five-row representative is not a clutter")
        if max(degrees(kernel, old_point_count)) > 3:
            raise AssertionError("saved five-row representative has point degree above three")
        if any(not 3 <= row.bit_count() <= 7 for row in kernel):
            raise AssertionError("saved five-row representative violates its row-size range")
        kernel_blockers = blockers(kernel)
        pair_count = sum(row.bit_count() == 2 for row in kernel_blockers)
        if len(kernel_blockers) not in (6, 7) or pair_count != 3:
            raise AssertionError("saved five-row representative has the wrong blocker profile")
        distribution_key = f"{len(kernel_blockers)}:{pair_count}"
        blocker_distribution[distribution_key] = blocker_distribution.get(distribution_key, 0) + 1

        x = old_point_count
        c0 = [row | (1 << x) if row.bit_count() == 2 else row for row in kernel_blockers]
        q_candidates = 0
        class_valid = 0
        if len(kernel_blockers) == 7:
            q_candidates = 1
            class_valid = int(valid_extension(c0, kernel, old_point_count + 1, x))
        else:
            c0_degrees = degrees(c0, old_point_count + 1)
            for chosen in range(1 << old_point_count):
                if any(
                    chosen & (1 << point) and c0_degrees[point] >= 3
                    for point in range(old_point_count)
                ):
                    continue
                for fresh in range(9 - chosen.bit_count()):
                    if fresh + chosen.bit_count() < 3:
                        continue
                    q = chosen
                    for index in range(fresh):
                        q |= 1 << (old_point_count + 1 + index)
                    candidate = [*c0, q]
                    if not is_clutter(candidate):
                        continue
                    q_candidates += 1
                    class_valid += int(
                        valid_extension(
                            candidate,
                            kernel,
                            old_point_count + 1 + fresh,
                            x,
                        )
                    )
        total_q_candidates += q_candidates
        valid_extensions += class_valid
        class_records.append(
            {
                "points": old_point_count,
                "blockers": len(kernel_blockers),
                "pairs": pair_count,
                "q_candidates": q_candidates,
                "valid_extensions": class_valid,
            }
        )
    if total_q_candidates != 55 or valid_extensions != 0:
        raise AssertionError("five-row extension totals do not match the claimed obstruction")
    return {
        "class_count": len(classes),
        "blocker_profiles": blocker_distribution,
        "total_q_candidates": total_q_candidates,
        "valid_extensions": valid_extensions,
        "classes": class_records,
    }


def check_four_row_class(classes: list[list[tuple[int, int]]]) -> dict[str, object]:
    if len(classes) != 1:
        raise AssertionError(f"expected 1 four-row class, found {len(classes)}")
    kernel, point_count = rows_from_class(classes[0], 4)
    kernel_blockers = blockers(kernel)
    support_multiset = sorted(
        support for support, count in classes[0] for _ in range(count)
    )
    expected = [3, 5, 6, 9, 10, 12]
    if support_multiset != expected:
        raise AssertionError("the unique four-row class is not the K4 edge incidence clutter")
    if len(kernel_blockers) != 7:
        raise AssertionError("the K4 kernel must have seven blockers")
    if sum(row.bit_count() == 2 for row in kernel_blockers) != 3:
        raise AssertionError("the K4 kernel must have three pair blockers")
    if max(degrees(kernel, point_count)) != 2:
        raise AssertionError("the K4 edge points must have kernel degree two")
    return {
        "class_count": 1,
        "points": point_count,
        "blockers": len(kernel_blockers),
        "pair_blockers": 3,
        "support_multiset": support_multiset,
    }


def check_three_row_integer_audit() -> dict[str, object]:
    solutions: list[tuple[int, ...]] = []
    for p, q, r, x, y, z in itertools.product(range(10), repeat=6):
        row_sizes = (p + x + y, q + x + z, r + y + z)
        if not all(3 <= size <= 9 for size in row_sizes):
            continue
        if not (p + y and q + z and p + x and r + z and q + x and r + y):
            continue
        pair_blockers = x * y + x * z + y * z + x * r + y * q + z * p
        triple_blockers = p * q * r
        if pair_blockers <= 5 and pair_blockers + triple_blockers <= 9:
            solutions.append((p, q, r, x, y, z, pair_blockers, triple_blockers))
    expected = {
        (1, 2, 2, 1, 1, 0, 5, 4),
        (2, 1, 2, 1, 0, 1, 5, 4),
        (2, 2, 1, 0, 1, 1, 5, 4),
    }
    if set(solutions) != expected:
        raise AssertionError("three-row integer classification changed")
    return {"labelled_solution_count": len(solutions), "solutions": solutions}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--four-row-results", type=Path, required=True)
    parser.add_argument("--five-row-results", type=Path, required=True)
    args = parser.parse_args()
    report = {
        "epistemic_label": "COMPUTED",
        "four_row": check_four_row_class(parse_classes(args.four_row_results)),
        "five_row": check_five_row_classes(parse_classes(args.five_row_results)),
        "three_row_integer_audit": check_three_row_integer_audit(),
        "verifier": "independent choice-union blocker minimization",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
