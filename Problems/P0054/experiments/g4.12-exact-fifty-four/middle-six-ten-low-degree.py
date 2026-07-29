#!/usr/bin/env python3
"""Enumerate the low-incidence equality kernels in the G4.12 (6,10) split."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

VERTICES = 6
SUPPORTS = tuple((vertex,) for vertex in range(VERTICES)) + tuple(
    itertools.combinations(range(VERTICES), 2)
)
SUPPORT_MASKS = tuple(sum(1 << vertex for vertex in support) for support in SUPPORTS)
FULL_MASK = (1 << VERTICES) - 1


def minimal_support_covers() -> tuple[tuple[int, ...], ...]:
    result = []
    for size in range(1, VERTICES + 1):
        for cover in itertools.combinations(range(len(SUPPORTS)), size):
            union = 0
            for index in cover:
                union |= SUPPORT_MASKS[index]
            if union != FULL_MASK:
                continue
            if all(
                any(
                    SUPPORT_MASKS[index] & (1 << vertex)
                    and all(
                        other == index or not SUPPORT_MASKS[other] & (1 << vertex)
                        for other in cover
                    )
                    for vertex in range(VERTICES)
                )
                for index in cover
            ):
                result.append(cover)
    return tuple(result)


COVERS = minimal_support_covers()


def blocker_profile(multiplicity: tuple[int, ...]) -> tuple[int, Counter[int]]:
    histogram: Counter[int] = Counter()
    for cover in COVERS:
        choices = 1
        for index in cover:
            choices *= multiplicity[index]
            if not choices:
                break
        histogram[len(cover)] += choices
    return sum(histogram.values()), histogram


def is_clutter(multiplicity: tuple[int, ...]) -> bool:
    for left in range(VERTICES):
        for right in range(VERTICES):
            if left == right:
                continue
            if all(
                not value or left not in support or right in support
                for support, value in zip(SUPPORTS, multiplicity, strict=True)
            ):
                return False
    return True


def matching_number(multiplicity: tuple[int, ...]) -> int:
    active_edges = tuple(
        support
        for support, value in zip(SUPPORTS, multiplicity, strict=True)
        if value and len(support) == 2
    )
    best = 0
    for size in range(1, 4):
        if any(
            len(set().union(*matching)) == 2 * size
            for matching in itertools.combinations(active_edges, size)
        ):
            best = size
    return best


def canonical_key(multiplicity: tuple[int, ...]) -> str:
    candidates = []
    for permutation in itertools.permutations(range(VERTICES)):
        transformed = []
        for support, value in zip(SUPPORTS, multiplicity, strict=True):
            if value:
                image = tuple(sorted(permutation[vertex] for vertex in support))
                transformed.append((image, value))
        candidates.append(tuple(sorted(transformed)))
    return ",".join(
        f"{''.join(str(vertex + 1) for vertex in support)}:{value}"
        for support, value in min(candidates)
    )


def enumerate_branch(
    low_count: int, class_data: dict[str, dict[str, object]]
) -> dict[str, object]:
    low = frozenset(range(low_count))
    allowed = tuple(
        index
        for index, support in enumerate(SUPPORTS)
        if any(vertex in low for vertex in support)
    )
    degree = [0] * VERTICES
    multiplicity = [0] * len(SUPPORTS)
    degree_vectors = 0
    clutter_vectors = 0
    labelled_kernels = 0
    core_matching_histogram: Counter[int] = Counter()
    core_minimum_blockers: dict[int, int] = {}
    clutter_matching_histogram: Counter[int] = Counter()
    clutter_minimum_blockers: dict[int, int] = {}

    def visit(position: int) -> None:
        nonlocal clutter_vectors, degree_vectors, labelled_kernels
        if position == len(allowed):
            if any(degree[vertex] != 3 for vertex in low):
                return
            if any(degree[vertex] < 4 for vertex in range(low_count, VERTICES)):
                return
            degree_vectors += 1
            current = tuple(multiplicity)
            blockers, histogram = blocker_profile(current)
            nu = matching_number(current)
            core_matching_histogram[nu] += 1
            core_minimum_blockers[nu] = min(
                core_minimum_blockers.get(nu, blockers), blockers
            )
            if not is_clutter(current):
                return
            clutter_vectors += 1
            clutter_matching_histogram[nu] += 1
            clutter_minimum_blockers[nu] = min(
                clutter_minimum_blockers.get(nu, blockers), blockers
            )
            if blockers != 10 or histogram[3] or nu != 2:
                return
            labelled_kernels += 1
            key = canonical_key(current)
            class_data.setdefault(
                key,
                {
                    "degree_sequence": sorted(degree),
                    "active_points": sum(current),
                    "blocker_size_histogram": {
                        str(size): count for size, count in sorted(histogram.items()) if count
                    },
                    "representative": key,
                },
            )
            return

        index = allowed[position]
        support = SUPPORTS[index]
        low_endpoints = tuple(vertex for vertex in support if vertex in low)
        capacity = min(3 - degree[vertex] for vertex in low_endpoints)
        for value in range(capacity + 1):
            multiplicity[index] = value
            for vertex in support:
                degree[vertex] += value
            visit(position + 1)
            for vertex in support:
                degree[vertex] -= value
        multiplicity[index] = 0

    visit(0)
    return {
        "degree_vectors": degree_vectors,
        "clutter_vectors": clutter_vectors,
        "core_matching_number_histogram": {
            str(value): core_matching_histogram[value]
            for value in sorted(core_matching_histogram)
        },
        "core_minimum_blockers_by_matching_number": {
            str(value): core_minimum_blockers[value]
            for value in sorted(core_minimum_blockers)
        },
        "clutter_matching_number_histogram": {
            str(value): clutter_matching_histogram[value]
            for value in sorted(clutter_matching_histogram)
        },
        "clutter_minimum_blockers_by_matching_number": {
            str(value): clutter_minimum_blockers[value]
            for value in sorted(clutter_minimum_blockers)
        },
        "target_ten_blocker_kernels": labelled_kernels,
    }


def enumerate_kernels() -> dict[str, object]:
    class_data: dict[str, dict[str, object]] = {}
    branches = {
        low_count: enumerate_branch(low_count, class_data) for low_count in (4, 5, 6)
    }

    return {
        "schema": "p0054.g4.12.middle-six-ten-low-degree.v1",
        "epistemic_label": "COMPUTED",
        "vertices": VERTICES,
        "supports": len(SUPPORTS),
        "minimal_support_covers": len(COVERS),
        "branches_by_degree_three_vertices": {
            str(low_count): branches[low_count] for low_count in (4, 5, 6)
        },
        "row_permutation_classes": len(class_data),
        "classes": [class_data[key] for key in sorted(class_data)],
    }


def exact_int(value: object) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError("expected integer")
    return value


def reference_summary(result: dict[str, object]) -> dict[str, int | str]:
    branches = result["branches_by_degree_three_vertices"]
    if not isinstance(branches, dict):
        raise TypeError("invalid branch summary")
    summary: dict[str, int | str] = {
        "schema": str(result["schema"]),
        "supports": exact_int(result["supports"]),
        "minimal_support_covers": exact_int(result["minimal_support_covers"]),
    }
    for low_count in (4, 5, 6):
        branch = branches[str(low_count)]
        if not isinstance(branch, dict):
            raise TypeError("invalid branch")
        prefix = f"low_{low_count}_"
        summary[prefix + "degree_vectors"] = int(branch["degree_vectors"])
        summary[prefix + "clutter_vectors"] = int(branch["clutter_vectors"])
        for kind in ("core", "clutter"):
            histogram = branch[f"{kind}_matching_number_histogram"]
            minima = branch[f"{kind}_minimum_blockers_by_matching_number"]
            if not isinstance(histogram, dict) or not isinstance(minima, dict):
                raise TypeError("invalid matching summary")
            for matching, count in histogram.items():
                summary[prefix + f"{kind}_matching_{matching}_vectors"] = int(count)
                summary[prefix + f"{kind}_matching_{matching}_minimum_blockers"] = int(
                    minima[matching]
                )
        summary[prefix + "target_ten_blocker_kernels"] = int(
            branch["target_ten_blocker_kernels"]
        )
    return summary


def parse_reference(path: Path) -> dict[str, int | str]:
    result: dict[str, int | str] = {}
    for line in path.read_text(encoding="ascii").splitlines():
        key, value = line.split("=", 1)
        result[key] = value if key == "schema" else int(value)
    return result


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    result = enumerate_kernels()
    reference = parse_reference(args.reference)
    actual = reference_summary(result)
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

    cpp_source = Path(__file__).with_suffix(".cpp")
    report = {
        "schema": "p0054.g4.12.middle-six-ten-low-degree-verification.v1",
        "epistemic_label": "COMPUTED",
        "reference_path": str(args.reference),
        "reference_sha256": sha256_file(args.reference),
        "cpp_source_sha256": sha256_file(cpp_source),
        "python_source_sha256": sha256_file(Path(__file__)),
        "independent_replay_match": True,
        "summary": result,
    }
    args.output.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="ascii"
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
