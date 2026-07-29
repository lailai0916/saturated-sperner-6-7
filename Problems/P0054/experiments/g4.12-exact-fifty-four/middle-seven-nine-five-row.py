#!/usr/bin/env python3
"""Check the frozen G4.11 five-row classes used in G4.12."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_supports(key: str) -> list[int]:
    result = []
    for term in key.split("|", 1)[0].rstrip(",").split(","):
        support, count = term.split(":")
        result.extend([int(support)] * int(count))
    return result


def row_sizes(supports: list[int]) -> list[int]:
    return [sum(bool(support & (1 << row)) for support in supports) for row in range(5)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    fields: dict[str, str] = {}
    classes = []
    for line in args.reference.read_text(encoding="ascii").splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        if key == "class":
            supports = parse_supports(value)
            sizes = sorted(row_sizes(supports))
            blockers = int(value.split("|b:", 1)[1].split("|", 1)[0])
            pairs = int(value.rsplit("|p:", 1)[1])
            classes.append(
                {
                    "key": value,
                    "row_sizes": sizes,
                    "blockers": blockers,
                    "pair_blockers": pairs,
                }
            )
        else:
            fields[key] = value

    if fields.get("multiplicity_vectors") != "490":
        raise AssertionError("frozen five-row vector count changed")
    if len(classes) != 8:
        raise AssertionError("expected eight frozen five-row classes")
    if any(row["row_sizes"][0] != 3 for row in classes):
        raise AssertionError("a frozen five-row class no longer has a three-point row")
    if any(row["pair_blockers"] != 3 for row in classes):
        raise AssertionError("frozen five-row pair-blocker count changed")
    if any(row["blockers"] not in (6, 7) for row in classes):
        raise AssertionError("frozen five-row blocker count changed")

    report = {
        "schema": "p0054.g4.12.middle-seven-nine-five-row.v1",
        "epistemic_label": "COMPUTED",
        "reference_path": str(args.reference),
        "reference_sha256": sha256_file(args.reference),
        "python_source_sha256": sha256_file(Path(__file__)),
        "multiplicity_vectors": 490,
        "row_permutation_classes": len(classes),
        "classes_with_minimum_row_three": len(classes),
        "classes_with_minimum_row_four": 0,
        "classes": classes,
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
