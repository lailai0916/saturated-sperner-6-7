#!/usr/bin/env python3
"""Independently verify the G4.12 six-row coupling enumeration."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from collections.abc import Iterator
from pathlib import Path

Profile = tuple[int, ...]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def transform(support: int, permutation: tuple[int, ...]) -> int:
    return sum(1 << permutation[row] for row in range(3) if support & (1 << row))


def canonical_profile(multiplicity: dict[int, int]) -> Profile:
    return min(
        tuple(
            sorted(
                transform(support, permutation)
                for support, count in multiplicity.items()
                for _ in range(count)
            )
        )
        for permutation in itertools.permutations(range(3))
    )


def marginal_profiles() -> tuple[int, tuple[Profile, ...]]:
    labelled = 0
    classes: set[Profile] = set()
    for p, q, r, x, y, z in itertools.product(range(6), repeat=6):
        sizes = (p + x + y, q + x + z, r + y + z)
        if any(not 2 <= size <= 5 for size in sizes):
            continue
        if not (p + y and q + z and p + x and r + z and q + x and r + y):
            continue
        pairs = x * y + x * z + y * z + x * r + y * q + z * p
        triples = p * q * r
        if pairs + triples > 4:
            continue
        labelled += 1
        classes.add(canonical_profile({1: p, 2: q, 4: r, 3: x, 5: y, 6: z}))
    return labelled, tuple(sorted(classes))


def partial_couplings(
    left: Profile,
    right: Profile,
    position: int = 0,
    used: frozenset[int] = frozenset(),
) -> Iterator[Profile]:
    if position == len(left):
        yield tuple(right[index] << 3 for index in range(len(right)) if index not in used)
        return
    for suffix in partial_couplings(left, right, position + 1, used):
        yield (left[position],) + suffix
    for index, support in enumerate(right):
        if index in used or left[position].bit_count() + support.bit_count() > 4:
            continue
        for suffix in partial_couplings(left, right, position + 1, used | {index}):
            yield (left[position] | (support << 3),) + suffix


def pair_blockers(supports: Profile) -> int:
    return sum(left | right == 63 for left, right in itertools.combinations(supports, 2))


def parse_reference(path: Path) -> dict[str, str]:
    return dict(
        line.split("=", 1) for line in path.read_text(encoding="ascii").splitlines() if "=" in line
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    labelled, profiles = marginal_profiles()
    histogram: Counter[int] = Counter()
    for left in profiles:
        for right in profiles:
            for coupling in partial_couplings(left + (7,), right + (7,)):
                histogram[pair_blockers((7, 56) + coupling)] += 1

    expected = {
        "schema": "p0054.g4.12.middle-seven-nine-six-row.v1",
        "marginal_labelled_solutions": str(labelled),
        "marginal_row_permutation_classes": str(len(profiles)),
        **{
            f"class_{index}": ",".join(
                f"{support}:{profile.count(support)}" for support in sorted(set(profile))
            )
            + ","
            for index, profile in enumerate(profiles, 1)
        },
        **{f"pair_blockers_{pairs}": str(count) for pairs, count in sorted(histogram.items())},
        "labelled_couplings": str(sum(histogram.values())),
        "minimum_pair_blockers": str(min(histogram)),
    }
    reference = parse_reference(args.reference)
    if reference != expected:
        raise AssertionError("independent six-row enumeration disagrees with reference")

    report = {
        "schema": "p0054.g4.12.middle-seven-nine-six-row-verification.v1",
        "epistemic_label": "COMPUTED",
        "reference_path": str(args.reference),
        "reference_sha256": sha256_file(args.reference),
        "python_source_sha256": sha256_file(Path(__file__)),
        "marginal_labelled_solutions": labelled,
        "marginal_row_permutation_classes": len(profiles),
        "labelled_couplings": sum(histogram.values()),
        "pair_blocker_histogram": {str(pairs): count for pairs, count in sorted(histogram.items())},
        "minimum_pair_blockers": min(histogram),
        "reference_match": True,
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
