#!/usr/bin/env python3
"""Exact incidence-pattern search for the frozen P0054 G4.3 blocker task.

The search represents a finite hypergraph H with r labelled members by the
nonzero incidence pattern of each active ground element.  Equal columns are
stored by a multiplicity, so column permutations are removed by construction;
row permutations are quotiented by ``canonical_multiplicities``.

For a supported pattern set P, a minimal transversal selects at most one copy
of each pattern.  Its pattern set Q is exactly an inclusion-minimal cover of
all r rows, and it has product(m[q] for q in Q) realisations.  This identity is
used by the search engine.  Two deliberately separate witness validators are
provided at the end of the file.
"""

from __future__ import annotations

import argparse
import itertools
import json
import platform
import sys
import time
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from typing import cast

PatternVector = tuple[int, ...]
Family = tuple[frozenset[int], ...]


@dataclass(frozen=True)
class Case:
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


def cases() -> list[Case]:
    answer: list[Case] = []
    for total in (8, 9, 10):
        for b in range(2, total - 3):
            a = total - b
            # Use the side with fewer rows.  At (5,5), using S gives the
            # stronger local min-transversal-size pruning.
            orientation = "S" if a <= b else "C"
            answer.append(Case(a, b, orientation))
    return answer


def row_permutations(r: int) -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.permutations(range(r)))


def permute_pattern(pattern: int, permutation: Sequence[int]) -> int:
    result = 0
    for old_row, new_row in enumerate(permutation):
        if pattern & (1 << old_row):
            result |= 1 << new_row
    return result


def canonical_multiplicities(
    multiplicities: PatternVector, r: int, permutations: Sequence[Sequence[int]]
) -> PatternVector:
    """Canonical form modulo permutations of the r hypergraph members."""
    images: list[PatternVector] = []
    for permutation in permutations:
        image = [0] * len(multiplicities)
        for pattern in range(1, 1 << r):
            image[permute_pattern(pattern, permutation) - 1] = multiplicities[pattern - 1]
        images.append(tuple(image))
    return min(images)


def is_clutter_support(support: Sequence[int], r: int) -> bool:
    """Rows are distinct and pairwise incomparable as subsets of columns."""
    for i in range(r):
        for j in range(i + 1, r):
            i_not_j = any((p & (1 << i)) and not (p & (1 << j)) for p in support)
            j_not_i = any((p & (1 << j)) and not (p & (1 << i)) for p in support)
            if not (i_not_j and j_not_i):
                return False
    return True


def minimal_pattern_covers(
    support: Sequence[int], r: int, count_cap: int, multiplicities: PatternVector
) -> tuple[list[tuple[int, ...]], int]:
    """Enumerate minimal covers of the row set and their weighted count."""
    full = (1 << r) - 1
    covers: list[tuple[int, ...]] = []
    weighted_count = 0
    # A minimal cover has at most r patterns: each member has a private row.
    for size in range(1, r + 1):
        for chosen in itertools.combinations(support, size):
            union = 0
            for pattern in chosen:
                union |= pattern
            if union != full:
                continue
            minimal = True
            for index, _pattern in enumerate(chosen):
                without = 0
                for other_index, other in enumerate(chosen):
                    if other_index != index:
                        without |= other
                if without == full:
                    minimal = False
                    break
            if not minimal:
                continue
            covers.append(chosen)
            weight = 1
            for pattern in chosen:
                weight *= multiplicities[pattern - 1]
            weighted_count += weight
            if weighted_count > count_cap:
                return covers, weighted_count
    return covers, weighted_count


def adding_support_preserves_minimum(
    support: Sequence[int], new_pattern: int, blocker_min: int, full: int
) -> bool:
    """Reject a support as soon as <= blocker_min-1 patterns cover all rows."""
    pool = tuple(support) + (new_pattern,)
    for size in range(1, blocker_min):
        for chosen in itertools.combinations(pool, size):
            union = 0
            for pattern in chosen:
                union |= pattern
            if union == full:
                return False
    return True


def explicit_family(
    multiplicities: PatternVector, r: int
) -> tuple[Family, list[int]]:
    patterns_by_vertex: list[int] = []
    for pattern in range(1, 1 << r):
        patterns_by_vertex.extend([pattern] * multiplicities[pattern - 1])
    rows: list[frozenset[int]] = []
    for row in range(r):
        rows.append(
            frozenset(
                vertex
                for vertex, pattern in enumerate(patterns_by_vertex)
                if pattern & (1 << row)
            )
        )
    return tuple(rows), patterns_by_vertex


def blocker_powerset(family: Family, ground_size: int) -> Family:
    """Validator A: direct scan of the full powerset, then inclusion filtering."""
    hitting: list[int] = []
    row_masks = [sum(1 << x for x in edge) for edge in family]
    for candidate in range(1 << ground_size):
        if all(candidate & edge for edge in row_masks):
            hitting.append(candidate)
    minimal_masks = [
        candidate
        for candidate in hitting
        if not any(other != candidate and (other & candidate) == other for other in hitting)
    ]
    return tuple(
        frozenset(x for x in range(ground_size) if mask & (1 << x))
        for mask in minimal_masks
    )


def blocker_choice_minimization(family: Family) -> Family:
    """Validator B: enumerate one chosen point per edge, then minimize unions.

    Every transversal contains such a choice union.  Keeping the
    inclusion-minimal choice unions therefore gives the complete blocker.
    This does not scan the ground-set powerset and does not use incidence
    patterns.
    """
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
    """Exhaustively compare both validators on every clutter on <=4 points.

    The same loop also compares the incidence-pattern weighted-cover formula
    used by the search with the explicit blocker cardinality and size multiset.
    """
    checked = 0
    formula_checked = 0
    empty_family_checked = False
    empty_edge_family_checked = False
    for ground_size in range(max_ground_size + 1):
        subsets = tuple(
            frozenset(x for x in range(ground_size) if mask & (1 << x))
            for mask in range(1 << ground_size)
        )
        for family_mask in range(1 << len(subsets)):
            family = tuple(
                edge for index, edge in enumerate(subsets) if family_mask & (1 << index)
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
                raise AssertionError("semantic validators disagree in exhaustive self-test")
            dual_a = blocker_powerset(blocker_a, ground_size)
            dual_b = blocker_choice_minimization(blocker_b)
            if normalize_family(dual_a) != normalize_family(family):
                raise AssertionError("powerset validator violates blocker involution")
            if normalize_family(dual_b) != normalize_family(family):
                raise AssertionError("choice validator violates blocker involution")
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
            support = [pattern for pattern in range(1, 1 << r) if vector[pattern - 1]]
            covers, weighted_count = minimal_pattern_covers(
                support, r, len(blocker_a), tuple(vector)
            )
            weighted_sizes: list[int] = []
            for cover in covers:
                weight = 1
                for pattern in cover:
                    weight *= vector[pattern - 1]
                weighted_sizes.extend([len(cover)] * weight)
            if weighted_count != len(blocker_a):
                raise AssertionError("incidence formula count disagrees with direct blocker")
            if sorted(weighted_sizes) != sorted(map(len, blocker_a)):
                raise AssertionError("incidence formula sizes disagree with direct blocker")
            formula_checked += 1
    return {
        "status": "PASS_COMPUTED",
        "max_ground_size": max_ground_size,
        "clutters_checked": checked,
        "incidence_formula_cases_checked": formula_checked,
        "empty_family_convention_checked": empty_family_checked,
        "singleton_empty_edge_family_checked": empty_edge_family_checked,
        "validators": ["direct_powerset", "edge_choice_union_minimization"],
    }


def validate_witness(
    multiplicities: PatternVector, case: Case
) -> dict[str, object]:
    primary, patterns_by_vertex = explicit_family(multiplicities, case.rows)
    blocker_a = blocker_powerset(primary, len(patterns_by_vertex))
    blocker_b = blocker_choice_minimization(primary)
    a_equal_b = normalize_family(blocker_a) == normalize_family(blocker_b)
    dual_a = blocker_powerset(blocker_a, len(patterns_by_vertex))
    dual_b = blocker_choice_minimization(blocker_b)
    target_s = primary if case.orientation == "S" else blocker_a
    target_c = blocker_a if case.orientation == "S" else primary
    expected_primary = normalize_family(primary)
    return {
        "ground_size": len(patterns_by_vertex),
        "vertex_incidence_patterns": patterns_by_vertex,
        "S": [list(edge) for edge in normalize_family(target_s)],
        "C": [list(edge) for edge in normalize_family(target_c)],
        "validator_powerset": {
            "B_primary": [list(edge) for edge in normalize_family(blocker_a)],
            "B_B_primary": [list(edge) for edge in normalize_family(dual_a)],
            "dual_equals_primary": normalize_family(dual_a) == expected_primary,
        },
        "validator_choice_minimization": {
            "B_primary": [list(edge) for edge in normalize_family(blocker_b)],
            "B_B_primary": [list(edge) for edge in normalize_family(dual_b)],
            "dual_equals_primary": normalize_family(dual_b) == expected_primary,
        },
        "validators_agree": a_equal_b and normalize_family(dual_a) == normalize_family(dual_b),
        "size_constraints": {
            "S_min_at_least_2": min(map(len, target_s)) >= 2,
            "C_min_at_least_4": min(map(len, target_c)) >= 4,
        },
    }


def search_case(case: Case) -> dict[str, object]:
    started = time.monotonic()
    r = case.rows
    full = (1 << r) - 1
    # A full incidence pattern would be a singleton blocker member, forbidden
    # in every requested case.  Other low-size covers are rejected incrementally.
    patterns = tuple(range(1, full))
    permutations = row_permutations(r)
    multiplicities = [0] * full
    row_sums = [0] * r
    counters: dict[str, int] = {
        "dfs_nodes": 0,
        "partial_blocker_count_prunes": 0,
        "complete_degree_vectors": 0,
        "canonical_representatives": 0,
        "clutter_representatives": 0,
        "blocker_count_evaluations": 0,
    }
    witnesses: list[dict[str, object]] = []

    # High-incidence columns first makes the small-transversal pruning early.
    ordered_patterns = tuple(sorted(patterns, key=lambda p: (-p.bit_count(), p)))

    def dfs(index: int, support: list[int]) -> None:
        counters["dfs_nodes"] += 1
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
            covers, weighted_count = minimal_pattern_covers(
                support, r, case.blocker_count, vector
            )
            if weighted_count != case.blocker_count:
                return
            if not covers or min(map(len, covers)) < case.blocker_min:
                return
            canonical = list(vector)
            validation = validate_witness(vector, case)
            if not validation["validators_agree"]:
                raise AssertionError("independent blocker validators disagree")
            size_constraints = cast(dict[str, bool], validation["size_constraints"])
            if not all(size_constraints.values()):
                raise AssertionError("reported witness violates requested size constraints")
            witnesses.append(
                {
                    "canonical_multiplicity_vector_patterns_1_to_2^r_minus_1": canonical,
                    "minimal_pattern_covers": [list(cover) for cover in covers],
                    "weighted_blocker_count": weighted_count,
                    "validation": validation,
                }
            )
            return

        pattern = ordered_patterns[index]
        rows = [row for row in range(r) if pattern & (1 << row)]
        cap = min(case.row_max - row_sums[row] for row in rows)

        # Multiplicity zero.
        dfs(index + 1, support)

        if cap <= 0 or not adding_support_preserves_minimum(
            support, pattern, case.blocker_min, full
        ):
            return
        support.append(pattern)
        for amount in range(1, cap + 1):
            multiplicities[pattern - 1] = amount
            for row in rows:
                row_sums[row] += 1
            # Every minimal cover using only the current support remains a
            # minimal cover after more patterns are added.  Its current
            # weighted count is therefore a monotone lower bound.
            _partial_covers, partial_count = minimal_pattern_covers(
                support, r, case.blocker_count, tuple(multiplicities)
            )
            if partial_count <= case.blocker_count:
                dfs(index + 1, support)
            else:
                counters["partial_blocker_count_prunes"] += 1
        for row in rows:
            row_sums[row] -= cap
        multiplicities[pattern - 1] = 0
        support.pop()

    dfs(0, [])
    elapsed = time.monotonic() - started
    return {
        "a": case.a,
        "b": case.b,
        "total": case.a + case.b,
        "orientation": case.orientation,
        "primary_rows": case.rows,
        "primary_member_size_range": [case.row_min, case.row_max],
        "required_blocker_count": case.blocker_count,
        "required_blocker_min_size": case.blocker_min,
        "status": "SAT_COMPUTED" if witnesses else "UNSAT_COMPUTED",
        "elapsed_seconds": elapsed,
        "coverage_counters": counters,
        "witnesses": witnesses,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--totals", nargs="+", type=int, default=[8, 9, 10])
    parser.add_argument(
        "--verify-results",
        help="structurally compare statuses/counters with a saved JSON result, ignoring timing",
    )
    args = parser.parse_args()
    requested = set(args.totals)
    selected = [case for case in cases() if case.a + case.b in requested]
    started = time.monotonic()
    semantic_validation = cross_validate_semantics()
    records = []
    for case in selected:
        record = search_case(case)
        records.append(record)
        print(
            f"finished total={record['total']} a={case.a} b={case.b} "
            f"status={record['status']} elapsed={record['elapsed_seconds']:.6f}s",
            file=sys.stderr,
            flush=True,
        )
    document = {
        "schema_version": 1,
        "epistemic_label": "COMPUTED",
        "random_seed": "NONE_DETERMINISTIC_EXHAUSTIVE_ENUMERATION",
        "python_version": platform.python_version(),
        "platform": platform.platform(),
        "command": (
            "uv run --offline python Problems/P0054/experiments/"
            "g4.3-stronger-lower/search.py --totals 8 9 10"
        ),
        "algorithm": (
            "incidence-pattern multiplicities; column-order quotient; "
            "row-permutation canonical minimum; exact minimal-pattern-cover weighting"
        ),
        "coverage_boundary": {
            "ground_set": "arbitrary finite U modulo deletion of inactive elements",
            "active_element_bound": (
                "at most a*b incidences; primary row sizes bounded by "
                "private-witness cardinality"
            ),
            "totals": [8, 9, 10],
            "splits": [[case.a, case.b] for case in selected],
            "warning": (
                "Finite quotient exhaustion is COMPUTED evidence only and is not a "
                "proof dependency or a general lower-bound proof."
            ),
        },
        "semantic_validation": semantic_validation,
        "elapsed_seconds": time.monotonic() - started,
        "cases": records,
    }
    if args.verify_results:
        with open(args.verify_results, encoding="utf-8") as handle:
            expected = json.load(handle)

        def stable_projection(value: dict[str, object]) -> dict[str, object]:
            projected_cases = []
            case_records = cast(list[dict[str, object]], value["cases"])
            for record in case_records:
                projected_cases.append(
                    {key: item for key, item in record.items() if key != "elapsed_seconds"}
                )
            return {
                "epistemic_label": value["epistemic_label"],
                "random_seed": value["random_seed"],
                "coverage_boundary": value["coverage_boundary"],
                "semantic_validation": value["semantic_validation"],
                "cases": projected_cases,
            }

        if stable_projection(document) != stable_projection(expected):
            raise SystemExit("STRUCTURAL_REPLAY_MISMATCH")
        print("STRUCTURAL_REPLAY_MATCH_COMPUTED", file=sys.stderr)
    json.dump(document, sys.stdout, indent=2, sort_keys=True)
    print()


if __name__ == "__main__":
    main()
