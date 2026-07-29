#!/usr/bin/env python3
"""Exact incidence search for the local parameter m(2,3).

The search reuses the independently cross-validated incidence engine from
G4.4. It enumerates exact multiplicities of all nonzero row-incidence
patterns, modulo row permutations. The private-witness injection bounds every
primary row size by the cardinality of its blocker, so the enumeration covers
arbitrary finite ground sets after inactive points are deleted.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import platform
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import cast

PatternVector = tuple[int, ...]

REPOSITORY_ROOT = Path(__file__).resolve().parents[4]
RELATIVE_SOURCE = "Problems/P0054/experiments/sat6-exact/search.py"
BASE_RELATIVE_SOURCE = "Problems/P0054/experiments/g4.4-exact-local/search.py"
BASE_SOURCE = REPOSITORY_ROOT / BASE_RELATIVE_SOURCE


def load_base_engine() -> ModuleType:
    spec = importlib.util.spec_from_file_location("p0054_g44_search", BASE_SOURCE)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load the G4.4 incidence engine")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


BASE = load_base_engine()


@dataclass(frozen=True)
class Case:
    """One ordered split (a,b), searched from the smaller side."""

    a: int
    b: int
    orientation: str

    @property
    def rows(self) -> int:
        return self.a if self.orientation == "S" else self.b

    @property
    def blocker_count(self) -> int:
        return self.b if self.orientation == "S" else self.a

    @property
    def row_min(self) -> int:
        return 2 if self.orientation == "S" else 3

    @property
    def row_max(self) -> int:
        return self.blocker_count

    @property
    def blocker_min(self) -> int:
        return 3 if self.orientation == "S" else 2


def all_cases() -> list[Case]:
    answer: list[Case] = []
    for total in range(5, 10):
        for a in range(3, total - 1):
            b = total - a
            if b < 2:
                continue
            orientation = "S" if a <= b else "C"
            answer.append(Case(a, b, orientation))
    return answer


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def validate_pair(
    primary: tuple[frozenset[int], ...],
    orientation: str,
    ground_size: int,
) -> dict[str, object]:
    blocker_a = BASE.blocker_powerset(primary, ground_size)
    blocker_b = BASE.blocker_choice_minimization(primary)
    dual_a = BASE.blocker_powerset(blocker_a, ground_size)
    dual_b = BASE.blocker_choice_minimization(blocker_b)
    target_s = primary if orientation == "S" else blocker_a
    target_c = blocker_a if orientation == "S" else primary

    normalized_primary = BASE.normalize_family(primary)
    normalized_blocker_a = BASE.normalize_family(blocker_a)
    normalized_blocker_b = BASE.normalize_family(blocker_b)
    normalized_dual_a = BASE.normalize_family(dual_a)
    normalized_dual_b = BASE.normalize_family(dual_b)
    normalized_s = BASE.normalize_family(target_s)
    normalized_c = BASE.normalize_family(target_c)
    return {
        "U": list(range(ground_size)),
        "S": [list(edge) for edge in normalized_s],
        "C": [list(edge) for edge in normalized_c],
        "validator_powerset": {
            "B_primary": [list(edge) for edge in normalized_blocker_a],
            "B_B_primary": [list(edge) for edge in normalized_dual_a],
            "B_B_primary_equals_primary": normalized_dual_a == normalized_primary,
        },
        "validator_choice_minimization": {
            "B_primary": [list(edge) for edge in normalized_blocker_b],
            "B_B_primary": [list(edge) for edge in normalized_dual_b],
            "B_B_primary_equals_primary": normalized_dual_b == normalized_primary,
        },
        "validators_agree_both_directions": (
            normalized_blocker_a == normalized_blocker_b
            and normalized_dual_a == normalized_dual_b
        ),
        "mutual_blocker_equalities": {
            "S_equals_B_C": (
                BASE.normalize_family(BASE.blocker_powerset(target_c, ground_size))
                == normalized_s
            ),
            "C_equals_B_S": (
                BASE.normalize_family(BASE.blocker_powerset(target_s, ground_size))
                == normalized_c
            ),
        },
        "size_constraints": {
            "S_min_at_least_2": min(map(len, target_s)) >= 2,
            "C_min_at_least_3": min(map(len, target_c)) >= 3,
        },
    }


def validate_witness(multiplicities: PatternVector, case: Case) -> dict[str, object]:
    primary, patterns_by_vertex = BASE.explicit_family(multiplicities, case.rows)
    validation = validate_pair(primary, case.orientation, len(patterns_by_vertex))
    validation["vertex_incidence_patterns"] = patterns_by_vertex
    return validation


def explicit_nine_member_witness() -> dict[str, object]:
    s = (
        frozenset((0, 2)),
        frozenset((0, 3)),
        frozenset((1, 2)),
        frozenset((1, 3)),
        frozenset((4, 5)),
    )
    c = (
        frozenset((0, 1, 4)),
        frozenset((0, 1, 5)),
        frozenset((2, 3, 4)),
        frozenset((2, 3, 5)),
    )
    validation = validate_pair(c, "C", 6)
    if BASE.normalize_family(s) != tuple(tuple(edge) for edge in validation["S"]):
        raise AssertionError("explicit witness has an unexpected blocker")
    if not cast(bool, validation["validators_agree_both_directions"]):
        raise AssertionError("explicit witness validators disagree")
    if not all(cast(dict[str, bool], validation["mutual_blocker_equalities"]).values()):
        raise AssertionError("explicit witness is not a mutual-blocker pair")
    if not all(cast(dict[str, bool], validation["size_constraints"]).values()):
        raise AssertionError("explicit witness violates the size constraints")
    validation["status"] = "PASS_COMPUTED"
    validation["total_members"] = len(s) + len(c)
    return validation


def stable_projection(document: dict[str, object]) -> dict[str, object]:
    cases = cast(list[dict[str, object]], document["cases"])
    projected_cases = [
        {key: value for key, value in record.items() if key != "elapsed_seconds"}
        for record in cases
    ]
    return {
        "schema_version": document["schema_version"],
        "epistemic_label": document["epistemic_label"],
        "source_sha256": document["source_sha256"],
        "base_engine_sha256": document["base_engine_sha256"],
        "algorithm": document["algorithm"],
        "coverage_boundary": document["coverage_boundary"],
        "semantic_validation": document["semantic_validation"],
        "explicit_nine_member_witness": document["explicit_nine_member_witness"],
        "cases": projected_cases,
        "assertions": document["assertions"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--per-case-seconds", type=float, default=900.0)
    parser.add_argument("--verify-results")
    args = parser.parse_args()
    if args.per_case_seconds <= 0 or args.per_case_seconds > 7200:
        raise SystemExit("--per-case-seconds must be in (0,7200]")

    BASE.validate_witness = validate_witness
    started = time.monotonic()
    semantic_validation = BASE.cross_validate_semantics()
    explicit_witness = explicit_nine_member_witness()
    records: list[dict[str, object]] = []
    for case in all_cases():
        record = cast(dict[str, object], BASE.search_case(case, args.per_case_seconds))
        records.append(record)
        print(
            f"finished total={record['total']} a={case.a} b={case.b} "
            f"status={record['status']} elapsed={record['elapsed_seconds']:.6f}s",
            file=sys.stderr,
            flush=True,
        )

    small_cases = [record for record in records if cast(int, record["total"]) <= 8]
    nine_cases = [record for record in records if record["total"] == 9]
    no_small_witness = all(record["status"] == "UNSAT_COMPUTED" for record in small_cases)
    complete_small_exhaustion = all(
        cast(bool, record["complete_exhaustion"]) for record in small_cases
    )
    search_found_nine = any(record["status"] == "SAT_COMPUTED" for record in nine_cases)
    assertions = {
        "all_totals_at_most_8_unsat_computed": no_small_witness,
        "all_totals_at_most_8_completely_exhausted": complete_small_exhaustion,
        "incidence_search_found_total_9": search_found_nine,
        "explicit_total_9_witness_verified": explicit_witness["status"] == "PASS_COMPUTED",
    }
    if not all(assertions.values()):
        raise AssertionError(f"search assertions failed: {assertions}")

    document: dict[str, object] = {
        "schema_version": 1,
        "epistemic_label": "COMPUTED",
        "source_sha256": sha256_file(Path(__file__).resolve()),
        "base_engine_sha256": sha256_file(BASE_SOURCE),
        "environment": {
            "network": "OFFLINE",
            "python_version": platform.python_version(),
            "platform": platform.platform(),
            "python_executable": sys.executable,
            "command": f"UV_OFFLINE=1 uv run --offline python {RELATIVE_SOURCE}",
            "per_case_seconds_limit": args.per_case_seconds,
            "elapsed_seconds": time.monotonic() - started,
        },
        "algorithm": (
            "exact nonzero incidence-pattern multiplicities, row-permutation "
            "canonicalization, and exact weighted minimal pattern covers"
        ),
        "coverage_boundary": {
            "ground_set": "arbitrary finite U after deletion of inactive points",
            "active_element_bound": (
                "the private-witness injection bounds each primary row size by "
                "the cardinality of the opposite blocker family"
            ),
            "ordered_splits": [[case.a, case.b] for case in all_cases()],
            "S_member_size_minimum": 2,
            "C_member_size_minimum": 3,
        },
        "semantic_validation": semantic_validation,
        "explicit_nine_member_witness": explicit_witness,
        "cases": records,
        "assertions": assertions,
    }

    if args.verify_results:
        expected = json.loads(Path(args.verify_results).read_text(encoding="utf-8"))
        if stable_projection(document) != stable_projection(expected):
            raise AssertionError("stable replay differs from saved results")
        print("STABLE_REPLAY_MATCH", file=sys.stderr)
    json.dump(document, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
