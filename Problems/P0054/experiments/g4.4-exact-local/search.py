#!/usr/bin/env python3
"""Deterministic exact incidence search for P0054 G4.4.

The primary clutter H has r labelled rows.  Every active ground element is
represented by its nonzero incidence pattern in {1, ..., 2^r-1}; equal
patterns have exact integer multiplicities.  Column order is therefore
removed by construction, and complete multiplicity vectors are quotiented by
row permutations.

For a fixed support, a minimal transversal contains at most one element of
each pattern.  Its patterns form an inclusion-minimal cover of all rows, and a
minimal pattern cover Q has exactly product(m[q] for q in Q) realisations.
All arithmetic used by the enumeration is integer arithmetic.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import platform
import resource
import sys
import time
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import cast

PatternVector = tuple[int, ...]
Family = tuple[frozenset[int], ...]

REPOSITORY_ROOT = Path(__file__).resolve().parents[4]
RELATIVE_SOURCE = "Problems/P0054/experiments/g4.4-exact-local/search.py"
FROZEN_INPUTS = (
    "AGENTS.md",
    "Problems/P0054/experiments/g4.4-exact-local/section0-freeze.md",
    "Problems/P0054/proof/g4.4-exact-local/frozen-subproblem.md",
    "Problems/P0054/literature/g4.4-exact-local/freeze-manifest.json",
    "Problems/P0054/experiments/g4.3-stronger-lower/search.py",
    "Problems/P0054/experiments/g4.3-stronger-lower/results.json",
    "Problems/P0054/experiments/g4.3-stronger-lower/report.md",
)


@dataclass(frozen=True)
class Case:
    """One requested ordered split (a,b), searched in one orientation."""

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
        return 2 if self.orientation == "S" else 4

    @property
    def row_max(self) -> int:
        return self.b if self.orientation == "S" else self.a

    @property
    def blocker_min(self) -> int:
        return 4 if self.orientation == "S" else 2


class CaseDeadlineExceeded(RuntimeError):
    """Raised when the explicit per-split resource boundary is reached."""


def all_cases() -> list[Case]:
    """All admissible splits for totals 9, 10, 11.

    The private-witness bound forces a>=4 and b>=2.  The orientation with
    fewer rows is searched; at a tie, S is used because its blocker-size lower
    bound is stronger.  The ordered (a,b) status is still reported explicitly.
    """

    answer: list[Case] = []
    for total in (9, 10, 11):
        for b in range(2, total - 3):
            a = total - b
            orientation = "S" if a <= b else "C"
            answer.append(Case(a, b, orientation))
    return answer


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def frozen_input_hashes() -> dict[str, str]:
    return {name: sha256_file(REPOSITORY_ROOT / name) for name in FROZEN_INPUTS}


def row_permutations(r: int) -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.permutations(range(r)))


def permute_pattern(pattern: int, permutation: Sequence[int]) -> int:
    result = 0
    for old_row, new_row in enumerate(permutation):
        if pattern & (1 << old_row):
            result |= 1 << new_row
    return result


def canonical_multiplicities(
    multiplicities: PatternVector,
    r: int,
    permutations: Sequence[Sequence[int]],
) -> PatternVector:
    """Lexicographic canonical form modulo all row permutations."""

    images: list[PatternVector] = []
    for permutation in permutations:
        image = [0] * len(multiplicities)
        for pattern in range(1, 1 << r):
            image[permute_pattern(pattern, permutation) - 1] = multiplicities[
                pattern - 1
            ]
        images.append(tuple(image))
    return min(images)


def is_clutter_support(support: Sequence[int], r: int) -> bool:
    """Check that the represented rows are distinct and incomparable."""

    for i in range(r):
        for j in range(i + 1, r):
            i_not_j = any(
                (pattern & (1 << i)) and not (pattern & (1 << j))
                for pattern in support
            )
            j_not_i = any(
                (pattern & (1 << j)) and not (pattern & (1 << i))
                for pattern in support
            )
            if not (i_not_j and j_not_i):
                return False
    return True


def minimal_pattern_covers(
    support: Sequence[int],
    r: int,
    count_cap: int,
    multiplicities: PatternVector,
) -> tuple[list[tuple[int, ...]], int]:
    """Return minimal row covers and their exact realised count.

    Enumeration may stop as soon as the exact count exceeds ``count_cap``;
    callers only need to distinguish equality from overflow.
    """

    full = (1 << r) - 1
    covers: list[tuple[int, ...]] = []
    weighted_count = 0
    for size in range(1, r + 1):
        for chosen in itertools.combinations(support, size):
            union = 0
            for pattern in chosen:
                union |= pattern
            if union != full:
                continue
            if any(
                _union_except(chosen, omitted_index) == full
                for omitted_index in range(len(chosen))
            ):
                continue
            covers.append(chosen)
            weight = 1
            for pattern in chosen:
                weight *= multiplicities[pattern - 1]
            weighted_count += weight
            if weighted_count > count_cap:
                return covers, weighted_count
    return covers, weighted_count


def _union_except(chosen: Sequence[int], omitted_index: int) -> int:
    union = 0
    for index, pattern in enumerate(chosen):
        if index != omitted_index:
            union |= pattern
    return union


def extend_minimal_covers(
    support: Sequence[int],
    old_covers: Sequence[tuple[int, ...]],
    new_pattern: int,
    r: int,
    blocker_min: int,
    count_cap: int,
) -> tuple[tuple[tuple[int, ...], ...], str]:
    """Increment the structural minimal-cover list after adding one pattern.

    Every old minimal cover remains minimal.  Every genuinely new minimal
    cover contains ``new_pattern``, so only combinations containing that
    pattern need to be tested.  Multiplicities are positive on the support;
    therefore more than ``count_cap`` structural covers already imply a
    realised blocker count above the cap for every multiplicity extension.
    """

    full = (1 << r) - 1
    extended = list(old_covers)
    for total_size in range(1, r + 1):
        for old_chosen in itertools.combinations(support, total_size - 1):
            chosen = old_chosen + (new_pattern,)
            union = 0
            for pattern in chosen:
                union |= pattern
            if union != full:
                continue
            if any(
                _union_except(chosen, omitted_index) == full
                for omitted_index in range(len(chosen))
            ):
                continue
            if total_size < blocker_min:
                return tuple(extended), "SMALL_COVER"
            extended.append(chosen)
            if len(extended) > count_cap:
                return tuple(extended), "STRUCTURAL_COUNT_OVERFLOW"
    return tuple(extended), "OK"


def weighted_cover_count(
    covers: Sequence[tuple[int, ...]],
    multiplicities: PatternVector,
    count_cap: int,
) -> int:
    """Exact realised blocker count, with an allowed early overflow return."""

    total = 0
    for cover in covers:
        weight = 1
        for pattern in cover:
            weight *= multiplicities[pattern - 1]
        total += weight
        if total > count_cap:
            return total
    return total


def explicit_family(
    multiplicities: PatternVector,
    r: int,
) -> tuple[Family, list[int]]:
    patterns_by_vertex: list[int] = []
    for pattern in range(1, 1 << r):
        patterns_by_vertex.extend([pattern] * multiplicities[pattern - 1])
    rows = tuple(
        frozenset(
            vertex
            for vertex, pattern in enumerate(patterns_by_vertex)
            if pattern & (1 << row)
        )
        for row in range(r)
    )
    return rows, patterns_by_vertex


def blocker_powerset(family: Family, ground_size: int) -> Family:
    """Validator A: scan the full powerset and filter minimal hitting sets."""

    row_masks = [sum(1 << element for element in edge) for edge in family]
    hitting: list[int] = []
    for candidate in range(1 << ground_size):
        if all(candidate & edge for edge in row_masks):
            hitting.append(candidate)
    minimal_masks = [
        candidate
        for candidate in hitting
        if not any(
            other != candidate and (other & candidate) == other for other in hitting
        )
    ]
    return tuple(
        frozenset(
            element
            for element in range(ground_size)
            if mask & (1 << element)
        )
        for mask in minimal_masks
    )


def blocker_choice_minimization(family: Family) -> Family:
    """Validator B: minimise unions of one independently chosen point per edge."""

    candidates = {frozenset(choice) for choice in itertools.product(*family)}
    ordered = sorted(candidates, key=lambda item: (len(item), tuple(sorted(item))))
    minimal: list[frozenset[int]] = []
    for candidate in ordered:
        if not any(old <= candidate for old in minimal):
            minimal.append(candidate)
    return tuple(minimal)


def normalize_family(
    family: Iterable[frozenset[int]],
) -> tuple[tuple[int, ...], ...]:
    return tuple(sorted(tuple(sorted(edge)) for edge in family))


def cross_validate_semantics(max_ground_size: int = 4) -> dict[str, object]:
    """Compare blockers and both cover engines on all small clutters."""

    checked = 0
    formula_checked = 0
    incremental_cover_checked = 0
    empty_family_checked = False
    empty_edge_family_checked = False
    for ground_size in range(max_ground_size + 1):
        subsets = tuple(
            frozenset(
                element
                for element in range(ground_size)
                if mask & (1 << element)
            )
            for mask in range(1 << ground_size)
        )
        for family_mask in range(1 << len(subsets)):
            family = tuple(
                edge
                for index, edge in enumerate(subsets)
                if family_mask & (1 << index)
            )
            if any(
                left != right and left <= right
                for left in family
                for right in family
            ):
                continue
            blocker_a = blocker_powerset(family, ground_size)
            blocker_b = blocker_choice_minimization(family)
            if normalize_family(blocker_a) != normalize_family(blocker_b):
                raise AssertionError("independent blocker validators disagree")
            dual_a = blocker_powerset(blocker_a, ground_size)
            dual_b = blocker_choice_minimization(blocker_b)
            if normalize_family(dual_a) != normalize_family(family):
                raise AssertionError("powerset validator violates involution")
            if normalize_family(dual_b) != normalize_family(family):
                raise AssertionError("choice validator violates involution")
            checked += 1
            empty_family_checked |= not family
            empty_edge_family_checked |= family == (frozenset(),)

            if not family:
                continue
            r = len(family)
            vector = [0] * ((1 << r) - 1)
            for vertex in range(ground_size):
                pattern = 0
                for row, edge in enumerate(family):
                    if vertex in edge:
                        pattern |= 1 << row
                if pattern:
                    vector[pattern - 1] += 1
            support = [
                pattern
                for pattern in range(1, 1 << r)
                if vector[pattern - 1]
            ]
            covers, weighted_count = minimal_pattern_covers(
                support,
                r,
                len(blocker_a),
                tuple(vector),
            )
            incremental_support: list[int] = []
            incremental_covers: tuple[tuple[int, ...], ...] = ()
            for pattern in support:
                incremental_covers, extension_status = extend_minimal_covers(
                    incremental_support,
                    incremental_covers,
                    pattern,
                    r,
                    blocker_min=1,
                    count_cap=1 << 30,
                )
                if extension_status != "OK":
                    raise AssertionError("incremental cover self-test overflowed")
                incremental_support.append(pattern)
            if sorted(incremental_covers) != sorted(covers):
                raise AssertionError(
                    "incremental and direct pattern-cover engines disagree"
                )
            incremental_weighted_count = weighted_cover_count(
                incremental_covers,
                tuple(vector),
                len(blocker_a),
            )
            if incremental_weighted_count != weighted_count:
                raise AssertionError(
                    "three-argument weighted cover API disagrees with direct engine"
                )
            incremental_cover_checked += 1
            weighted_sizes: list[int] = []
            for cover in covers:
                weight = 1
                for pattern in cover:
                    weight *= vector[pattern - 1]
                weighted_sizes.extend([len(cover)] * weight)
            if weighted_count != len(blocker_a):
                raise AssertionError("incidence count disagrees with direct blocker")
            if sorted(weighted_sizes) != sorted(map(len, blocker_a)):
                raise AssertionError("incidence sizes disagree with direct blocker")
            formula_checked += 1
    return {
        "status": "PASS_COMPUTED",
        "max_ground_size": max_ground_size,
        "clutters_checked": checked,
        "incidence_formula_cases_checked": formula_checked,
        "incremental_cover_cases_checked": incremental_cover_checked,
        "weighted_cover_count_three_argument_api_checked": True,
        "empty_family_convention_checked": empty_family_checked,
        "singleton_empty_edge_family_checked": empty_edge_family_checked,
        "validators": [
            "direct_powerset",
            "edge_choice_union_minimization",
        ],
    }


def validate_witness(
    multiplicities: PatternVector,
    case: Case,
) -> dict[str, object]:
    """Save complete U,S,C and verify both blocker directions independently."""

    primary, patterns_by_vertex = explicit_family(multiplicities, case.rows)
    blocker_a = blocker_powerset(primary, len(patterns_by_vertex))
    blocker_b = blocker_choice_minimization(primary)
    dual_a = blocker_powerset(blocker_a, len(patterns_by_vertex))
    dual_b = blocker_choice_minimization(blocker_b)
    target_s = primary if case.orientation == "S" else blocker_a
    target_c = blocker_a if case.orientation == "S" else primary
    normalized_primary = normalize_family(primary)
    normalized_blocker_a = normalize_family(blocker_a)
    normalized_blocker_b = normalize_family(blocker_b)
    normalized_dual_a = normalize_family(dual_a)
    normalized_dual_b = normalize_family(dual_b)
    return {
        "U": list(range(len(patterns_by_vertex))),
        "vertex_incidence_patterns": patterns_by_vertex,
        "S": [list(edge) for edge in normalize_family(target_s)],
        "C": [list(edge) for edge in normalize_family(target_c)],
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
                normalize_family(blocker_powerset(target_c, len(patterns_by_vertex)))
                == normalize_family(target_s)
            ),
            "C_equals_B_S": (
                normalize_family(blocker_powerset(target_s, len(patterns_by_vertex)))
                == normalize_family(target_c)
            ),
        },
        "size_constraints": {
            "S_min_at_least_2": min(map(len, target_s)) >= 2,
            "C_min_at_least_4": min(map(len, target_c)) >= 4,
        },
    }


def search_case(case: Case, per_case_seconds: float) -> dict[str, object]:
    started = time.monotonic()
    deadline = started + per_case_seconds
    r = case.rows
    full = (1 << r) - 1
    # The full incidence pattern alone hits every row and is forbidden because
    # every requested blocker member must have size at least two.
    patterns = tuple(range(1, full))
    ordered_patterns = tuple(
        sorted(patterns, key=lambda pattern: (-pattern.bit_count(), pattern))
    )
    permutations = row_permutations(r)
    multiplicities = [0] * full
    row_sums = [0] * r
    counters: dict[str, int] = {
        "dfs_nodes": 0,
        "deadline_checks": 0,
        "partial_small_cover_prunes": 0,
        "partial_structural_cover_count_prunes": 0,
        "partial_blocker_count_prunes": 0,
        "complete_degree_vectors": 0,
        "canonical_representatives": 0,
        "clutter_representatives": 0,
        "blocker_count_evaluations": 0,
        "sat_canonical_vectors": 0,
    }
    first_witness: dict[str, object] | None = None

    def check_deadline() -> None:
        counters["deadline_checks"] += 1
        if time.monotonic() >= deadline:
            raise CaseDeadlineExceeded

    def dfs(
        index: int,
        support: list[int],
        covers: tuple[tuple[int, ...], ...],
    ) -> None:
        nonlocal first_witness
        counters["dfs_nodes"] += 1
        if counters["dfs_nodes"] & 65535 == 0:
            check_deadline()
        if index == len(ordered_patterns):
            if any(value < case.row_min for value in row_sums):
                return
            counters["complete_degree_vectors"] += 1
            vector = tuple(multiplicities)
            if vector != canonical_multiplicities(vector, r, permutations):
                return
            counters["canonical_representatives"] += 1
            if not is_clutter_support(support, r):
                return
            counters["clutter_representatives"] += 1
            counters["blocker_count_evaluations"] += 1
            weighted_count = weighted_cover_count(
                covers,
                vector,
                case.blocker_count,
            )
            if weighted_count != case.blocker_count:
                return
            if not covers or min(map(len, covers)) < case.blocker_min:
                return
            counters["sat_canonical_vectors"] += 1
            if first_witness is None:
                validation = validate_witness(vector, case)
                validators_agree = cast(
                    bool,
                    validation["validators_agree_both_directions"],
                )
                size_constraints = cast(
                    dict[str, bool],
                    validation["size_constraints"],
                )
                mutual_equalities = cast(
                    dict[str, bool],
                    validation["mutual_blocker_equalities"],
                )
                if not validators_agree:
                    raise AssertionError("witness blocker validators disagree")
                if not all(size_constraints.values()):
                    raise AssertionError("witness violates size constraints")
                if not all(mutual_equalities.values()):
                    raise AssertionError("witness violates mutual blocker equality")
                first_witness = {
                    "canonical_multiplicity_vector_patterns_1_to_2^r_minus_1": (
                        list(vector)
                    ),
                    "minimal_pattern_covers": [list(cover) for cover in covers],
                    "weighted_blocker_count": weighted_count,
                    "validation": validation,
                }
            return

        pattern = ordered_patterns[index]
        rows = [row for row in range(r) if pattern & (1 << row)]
        cap = min(case.row_max - row_sums[row] for row in rows)

        dfs(index + 1, support, covers)

        if cap <= 0:
            return
        extended_covers, extension_status = extend_minimal_covers(
            support,
            covers,
            pattern,
            r,
            case.blocker_min,
            case.blocker_count,
        )
        if extension_status == "SMALL_COVER":
            counters["partial_small_cover_prunes"] += 1
            return
        if extension_status == "STRUCTURAL_COUNT_OVERFLOW":
            counters["partial_structural_cover_count_prunes"] += 1
            return
        support.append(pattern)
        for amount in range(1, cap + 1):
            multiplicities[pattern - 1] += 1
            for row in rows:
                row_sums[row] += 1
            partial_count = weighted_cover_count(
                extended_covers,
                tuple(multiplicities),
                case.blocker_count,
            )
            if partial_count <= case.blocker_count:
                dfs(index + 1, support, extended_covers)
            else:
                counters["partial_blocker_count_prunes"] += cap - amount + 1
                remaining = cap - amount
                if remaining:
                    for row in rows:
                        row_sums[row] += remaining
                    multiplicities[pattern - 1] += remaining
                break
        for row in rows:
            row_sums[row] -= cap
        multiplicities[pattern - 1] = 0
        support.pop()

    timed_out = False
    try:
        check_deadline()
        dfs(0, [], ())
    except CaseDeadlineExceeded:
        timed_out = True
    elapsed = time.monotonic() - started
    if timed_out:
        status = "TIMEOUT_NO_EVIDENCE"
    elif first_witness is None:
        status = "UNSAT_COMPUTED"
    else:
        status = "SAT_COMPUTED"
    return {
        "a": case.a,
        "b": case.b,
        "total": case.a + case.b,
        "orientation": case.orientation,
        "orientation_reason": (
            "searched the side with fewer rows; S is used at a tie"
        ),
        "primary_rows": case.rows,
        "primary_member_size_range": [case.row_min, case.row_max],
        "required_blocker_count": case.blocker_count,
        "required_blocker_min_size": case.blocker_min,
        "status": status,
        "complete_exhaustion": not timed_out,
        "elapsed_seconds": elapsed,
        "coverage_counters": counters,
        "first_witness": first_witness,
    }


def stable_projection(document: dict[str, object]) -> dict[str, object]:
    """Projection compared on replay: ignore wall time, retain every counter."""

    projected_cases = []
    cases = cast(list[dict[str, object]], document["cases"])
    for record in cases:
        projected_cases.append(
            {
                key: value
                for key, value in record.items()
                if key != "elapsed_seconds"
            }
        )
    return {
        "schema_version": document["schema_version"],
        "epistemic_label": document["epistemic_label"],
        "random_seed": document["random_seed"],
        "source_sha256": document["source_sha256"],
        "frozen_input_sha256": document["frozen_input_sha256"],
        "algorithm": document["algorithm"],
        "coverage_boundary": document["coverage_boundary"],
        "semantic_validation": document["semantic_validation"],
        "cases": projected_cases,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--totals", nargs="+", type=int, default=[9, 10, 11])
    parser.add_argument("--per-case-seconds", type=float, default=7200.0)
    parser.add_argument(
        "--verify-results",
        help="compare all structure and counters with saved JSON, ignoring wall time",
    )
    args = parser.parse_args()
    if args.per_case_seconds <= 0 or args.per_case_seconds > 7200:
        raise SystemExit("--per-case-seconds must be in (0,7200]")
    requested = set(args.totals)
    if not requested <= {9, 10, 11}:
        raise SystemExit("--totals may contain only 9, 10, 11")
    selected = [
        case for case in all_cases() if case.a + case.b in requested
    ]
    started = time.monotonic()
    semantic_validation = cross_validate_semantics()
    records = []
    for case in selected:
        record = search_case(case, args.per_case_seconds)
        records.append(record)
        print(
            f"finished total={record['total']} a={case.a} b={case.b} "
            f"status={record['status']} elapsed={record['elapsed_seconds']:.6f}s",
            file=sys.stderr,
            flush=True,
        )
    command = (
        "UV_OFFLINE=1 uv run --offline python "
        f"{RELATIVE_SOURCE} --totals "
        + " ".join(map(str, args.totals))
    )
    document: dict[str, object] = {
        "schema_version": 2,
        "epistemic_label": "COMPUTED",
        "random_seed": "NONE_DETERMINISTIC_EXHAUSTIVE_ENUMERATION",
        "source_sha256": sha256_file(Path(__file__).resolve()),
        "frozen_input_sha256": frozen_input_hashes(),
        "environment": {
            "network": "OFFLINE",
            "python_version": platform.python_version(),
            "platform": platform.platform(),
            "python_executable": sys.executable,
            "command": command,
            "per_case_seconds_limit": args.per_case_seconds,
            "temporary_disk_limit_gb": 30,
            "temporary_search_files_created": 0,
        },
        "algorithm": (
            "canonical nonzero incidence-pattern multiplicities; column-order "
            "quotient by exact multiplicities; complete row-permutation canonical "
            "minimum; exact integer minimal-pattern-cover weighting; monotone "
            "partial blocker-count and small-cover pruning"
        ),
        "coverage_boundary": {
            "ground_set": (
                "arbitrary finite U after deletion of elements in no primary row"
            ),
            "active_element_bound": (
                "primary row sizes are at most the blocker family cardinality "
                "by the private-witness injection; every multiplicity is bounded "
                "by a primary row upper bound"
            ),
            "assumptions": [
                "ordinary set families rather than multisets",
                "both sides are finite clutters",
                "inactive ground elements are irrelevant to minimal transversals",
                "repeated nonzero incidence patterns are retained by multiplicity",
                "row sizes may be nonuniform and incidence classes may be empty",
            ],
            "totals": sorted(requested),
            "splits": [[case.a, case.b] for case in selected],
            "duality_and_nonduplication": (
                "every ordered split receives a status; one orientation is enough "
                "because B(B(H))=H for finite clutters, and choosing the fewer-row "
                "side avoids a duplicate oriented computation"
            ),
            "warning": (
                "Finite quotient exhaustion is COMPUTED evidence only; timeout "
                "would be TIMEOUT_NO_EVIDENCE, and no global theorem follows here."
            ),
        },
        "semantic_validation": semantic_validation,
        "elapsed_seconds": time.monotonic() - started,
        "resource_usage": {
            "peak_resident_set_size_raw": resource.getrusage(
                resource.RUSAGE_SELF
            ).ru_maxrss,
            "peak_resident_set_size_unit": (
                "bytes_on_macos_kibibytes_on_linux"
            ),
            "temporary_search_bytes": 0,
        },
        "replay_policy": (
            "stable_projection ignores elapsed_seconds and resource_usage but "
            "compares every case status, witness, and structural counter"
        ),
        "cases": records,
    }
    if args.verify_results:
        with Path(args.verify_results).open(encoding="utf-8") as handle:
            expected = cast(dict[str, object], json.load(handle))
        if stable_projection(document) != stable_projection(expected):
            raise SystemExit("STRUCTURAL_REPLAY_MISMATCH")
        print("STRUCTURAL_REPLAY_MATCH_COMPUTED", file=sys.stderr)
    json.dump(document, sys.stdout, indent=2, sort_keys=True)
    print()


if __name__ == "__main__":
    main()
