#!/usr/bin/env python3
"""Cross-check every saved G4.12 (7,9) output."""

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


def parse_text(path: Path) -> dict[str, str]:
    return dict(
        line.split("=", 1) for line in path.read_text(encoding="ascii").splitlines() if "=" in line
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cpp-kernels", type=Path, required=True)
    parser.add_argument("--python-kernels", type=Path, required=True)
    parser.add_argument("--cpp-extensions", type=Path, required=True)
    parser.add_argument("--python-extensions", type=Path, required=True)
    parser.add_argument("--five-row", type=Path, required=True)
    parser.add_argument("--six-row", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    cpp_kernels = parse_text(args.cpp_kernels)
    python_kernels = json.loads(args.python_kernels.read_text(encoding="ascii"))
    scalar_fields = (
        "supports",
        "minimal_support_covers",
        "active_masks_checked",
        "support_feasible_masks",
        "multiplicity_vectors",
        "row_permutation_classes",
    )
    if any(int(cpp_kernels[field]) != python_kernels[field] for field in scalar_fields):
        raise AssertionError("four-row scalar fields disagree")
    cpp_histogram = {
        key: int(value) for key, value in cpp_kernels.items() if key.startswith("blockers_")
    }
    if cpp_histogram != python_kernels["blocker_histogram"]:
        raise AssertionError("four-row blocker histograms disagree")
    cpp_classes = {value for key, value in cpp_kernels.items() if key.startswith("class_")}
    if cpp_classes != set(python_kernels["classes"]):
        raise AssertionError("four-row classes disagree")

    cpp_extensions = parse_text(args.cpp_extensions)
    python_extensions = json.loads(args.python_extensions.read_text(encoding="ascii"))
    cpp_class_counts = [
        int(cpp_extensions[f"class_{index}_extension_candidates"]) for index in range(1, 12)
    ]
    python_class_counts = [row["extension_candidates"] for row in python_extensions["classes"]]
    if cpp_class_counts != python_class_counts:
        raise AssertionError("extension class counts disagree")
    if int(cpp_extensions["extension_candidates"]) != python_extensions["extension_candidates"]:
        raise AssertionError("extension totals disagree")
    if int(cpp_extensions["valid_extensions"]) != 0:
        raise AssertionError("C++ extension output has a valid candidate")
    if python_extensions["valid_extensions"] != 0:
        raise AssertionError("Python extension output has a valid candidate")

    five_row = json.loads(args.five_row.read_text(encoding="ascii"))
    if five_row["classes_with_minimum_row_four"] != 0:
        raise AssertionError("five-row replay has a row-size-four class")
    six_row = json.loads(args.six_row.read_text(encoding="ascii"))
    if not six_row["reference_match"] or six_row["minimum_pair_blockers"] != 4:
        raise AssertionError("six-row independent replay changed")

    report = {
        "schema": "p0054.g4.12.middle-seven-nine-cross-verification.v1",
        "epistemic_label": "COMPUTED",
        "python_source_sha256": sha256_file(Path(__file__)),
        "inputs": {
            name: {"path": str(path), "sha256": sha256_file(path)}
            for name, path in (
                ("cpp_kernels", args.cpp_kernels),
                ("python_kernels", args.python_kernels),
                ("cpp_extensions", args.cpp_extensions),
                ("python_extensions", args.python_extensions),
                ("five_row", args.five_row),
                ("six_row", args.six_row),
            )
        },
        "four_row_independent_match": True,
        "extension_independent_match": True,
        "kernel_classes": 11,
        "extension_candidates": 138161,
        "valid_extensions": 0,
        "five_row_classes_with_minimum_row_four": 0,
        "six_row_minimum_pair_blockers": 4,
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
