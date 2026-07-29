from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

LINES = (
    frozenset((0, 1, 2)),
    frozenset((0, 3, 4)),
    frozenset((0, 5, 6)),
    frozenset((1, 3, 5)),
    frozenset((1, 4, 6)),
    frozenset((2, 3, 6)),
    frozenset((2, 4, 5)),
)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blockers(rows: tuple[frozenset[int], ...], points: tuple[int, ...]) -> set[frozenset[int]]:
    result: set[frozenset[int]] = set()
    for size in range(1, len(points) + 1):
        for chosen in itertools.combinations(points, size):
            candidate = frozenset(chosen)
            if all(candidate & row for row in rows) and not any(
                previous < candidate for previous in result
            ):
                result.add(candidate)
    return result


def internal_blockers(
    edges: tuple[frozenset[int], ...], active_part: frozenset[int]
) -> set[frozenset[int]]:
    if not active_part:
        return set()
    return blockers((*edges, active_part), tuple(range(7)))


def extended_blockers(
    edges: tuple[frozenset[int], ...],
    base_blockers: set[frozenset[int]],
    active_part: frozenset[int],
    outside_count: int,
) -> set[frozenset[int]]:
    result = internal_blockers(edges, active_part)
    outside = tuple(range(7, 7 + outside_count))
    for cover in base_blockers:
        if cover & active_part:
            continue
        for point in outside:
            result.add(cover | frozenset((point,)))
    return result


def parse_reference(path: Path) -> dict[str, int | str]:
    result: dict[str, int | str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        key, value = line.split("=", 1)
        result[key] = value if key == "schema" else int(value)
    return result


def enumerate_summary() -> dict[str, int | str]:
    summary: dict[str, int | str] = {
        "schema": "p0054.g4.12.fano-adjacency.v1",
        "fano_graphs": 0,
        "split_7_6_admissible": 0,
        "split_7_6_target_hits": 0,
        "split_8_5_candidates": 0,
        "split_8_5_five_blockers": 0,
        "split_8_5_admissible": 0,
        "split_8_5_target_hits": 0,
    }

    for choices in itertools.product(range(3), repeat=7):
        edges = tuple(
            frozenset(tuple(itertools.combinations(sorted(line), 2))[choice])
            for line, choice in zip(LINES, choices, strict=True)
        )
        if len(set(edges)) != 7:
            raise AssertionError("selected Fano edges must be distinct")
        summary["fano_graphs"] = int(summary["fano_graphs"]) + 1
        base = blockers(edges, tuple(range(7)))
        if min(map(len, base)) >= 4:
            summary["split_7_6_admissible"] = int(summary["split_7_6_admissible"]) + 1
            key = f"split_7_6_blockers_{len(base)}"
            summary[key] = int(summary.get(key, 0)) + 1
            if len(base) == 6:
                summary["split_7_6_target_hits"] = int(summary["split_7_6_target_hits"]) + 1

        for bits in range(1 << 7):
            active_part = frozenset(point for point in range(7) if bits & (1 << point))
            if any(edge <= active_part for edge in edges):
                continue
            for outside_count in range(6 - len(active_part)):
                if len(active_part) + outside_count < 2:
                    continue
                summary["split_8_5_candidates"] = int(summary["split_8_5_candidates"]) + 1
                current = extended_blockers(edges, base, active_part, outside_count)
                minimum = min(map(len, current))
                if len(current) == 5:
                    summary["split_8_5_five_blockers"] = int(
                        summary["split_8_5_five_blockers"]
                    ) + 1
                    key = f"split_8_5_five_minimum_{minimum}"
                    summary[key] = int(summary.get(key, 0)) + 1
                if minimum >= 4:
                    summary["split_8_5_admissible"] = int(summary["split_8_5_admissible"]) + 1
                    key = f"split_8_5_blockers_{len(current)}"
                    summary[key] = int(summary.get(key, 0)) + 1
                    if len(current) == 5:
                        summary["split_8_5_target_hits"] = int(
                            summary["split_8_5_target_hits"]
                        ) + 1
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    reference = parse_reference(args.reference)
    actual = enumerate_summary()
    if actual != reference:
        missing = sorted(set(reference) - set(actual))
        extra = sorted(set(actual) - set(reference))
        mismatched = sorted(
            key for key in set(reference) & set(actual) if reference[key] != actual[key]
        )
        raise AssertionError({"missing": missing, "extra": extra, "mismatched": mismatched})

    source = Path(__file__).with_name("fano-adjacency.cpp")
    report = {
        "schema": "p0054.g4.12.fano-adjacency-verification.v1",
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
