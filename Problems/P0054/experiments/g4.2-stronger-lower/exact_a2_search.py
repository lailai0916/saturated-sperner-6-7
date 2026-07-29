#!/usr/bin/env python3
"""Exact finite and incidence-quotient checks for a seven-member P0054 A2.

All conclusions emitted by this program are COMPUTED.  In particular, the
arbitrary-q incidence quotient is not an external UNSAT certificate and is
not promoted to a proof of the frozen theorem candidate.
"""

from __future__ import annotations

import argparse
import itertools
import json
import platform
import sys
from collections.abc import Iterable
from typing import Any

import z3  # type: ignore[import-untyped]


def is_subset(left: int, right: int) -> bool:
    return left & ~right == 0


def masks_to_sets(masks: Iterable[int], q: int) -> list[list[int]]:
    return [[x for x in range(q) if mask >> x & 1] for mask in masks]


def incomparable(masks: list[int]) -> bool:
    return all(
        not is_subset(left, right) and not is_subset(right, left)
        for index, left in enumerate(masks)
        for right in masks[index + 1 :]
    )


def direct_oriented_validator(
    q: int,
    small: list[int],
    complements: list[int],
    *,
    expected_total: int | None = 7,
) -> dict[str, Any]:
    """Validator A: enumerate every R and check the oriented cover directly."""

    full = (1 << q) - 1
    failures: list[str] = []
    if expected_total is not None and len(small) + len(complements) != expected_total:
        failures.append("wrong_total")
    if len(set(small)) != len(small) or len(set(complements)) != len(complements):
        failures.append("duplicate_member")
    if any(mask & ~full for mask in [*small, *complements]):
        failures.append("mask_outside_ground_set")
    if any(mask.bit_count() < 2 for mask in small):
        failures.append("small_size_below_2")
    if any(mask.bit_count() < 4 for mask in complements):
        failures.append("complement_size_below_4")
    if not incomparable(small):
        failures.append("small_not_clutter")
    if not incomparable(complements):
        failures.append("complements_not_clutter")
    if any(s_mask & c_mask == 0 for s_mask in small for c_mask in complements):
        failures.append("cross_disjoint_pair")

    uncovered: list[int] = []
    multiplicity_digest: list[int] = []
    for r_mask in range(1 << q):
        multiplicity = sum(is_subset(s_mask, r_mask) for s_mask in small)
        multiplicity += sum(r_mask & c_mask == 0 for c_mask in complements)
        multiplicity_digest.append(multiplicity)
        if multiplicity == 0:
            uncovered.append(r_mask)
    if uncovered:
        failures.append("oriented_coverage_failure")
    return {
        "validator": "direct_oriented_all_R",
        "accepted": not failures,
        "failures": failures,
        "R_checked": 1 << q,
        "uncovered_R_masks": uncovered,
        "coverage_multiplicity_min": min(multiplicity_digest, default=0),
        "coverage_multiplicity_max": max(multiplicity_digest, default=0),
    }


def minimal_transversals(q: int, edges: list[int]) -> list[int]:
    transversals = [
        mask
        for mask in range(1 << q)
        if all(mask & edge for edge in edges)
    ]
    return [
        mask
        for mask in transversals
        if all(
            not all((mask ^ (1 << x)) & edge for edge in edges)
            for x in range(q)
            if mask >> x & 1
        )
    ]


def blocker_validator(
    q: int,
    small: list[int],
    complements: list[int],
    *,
    expected_total: int | None = 7,
) -> dict[str, Any]:
    """Validator B: independently compute both blocker families."""

    blocker_of_complements = minimal_transversals(q, complements)
    blocker_of_small = minimal_transversals(q, small)
    failures: list[str] = []
    if expected_total is not None and len(small) + len(complements) != expected_total:
        failures.append("wrong_total")
    if sorted(small) != blocker_of_complements:
        failures.append("small_not_blocker_of_complements")
    if sorted(complements) != blocker_of_small:
        failures.append("complements_not_blocker_of_small")
    if any(mask.bit_count() < 2 for mask in small):
        failures.append("small_size_below_2")
    if any(mask.bit_count() < 4 for mask in complements):
        failures.append("complement_size_below_4")
    return {
        "validator": "independent_blocker_involution",
        "accepted": not failures,
        "failures": failures,
        "blocker_of_complements_masks": blocker_of_complements,
        "blocker_of_small_masks": blocker_of_small,
    }


def relabel_mask(mask: int, order: tuple[int, ...]) -> int:
    result = 0
    for new_x, old_x in enumerate(order):
        if mask >> old_x & 1:
            result |= 1 << new_x
    return result


def canonicalize_witness(q: int, small: list[int], complements: list[int]) -> dict[str, Any]:
    """Canonical label under ground, small-row, and complement-row permutations.

    For fixed row orders, equal-incidence ground points are consecutive and
    columns are sorted by their full membership signature.  Exhausting the at
    most 7! row permutations then selects the lexicographically least form.
    """

    best: tuple[tuple[int, ...], tuple[int, ...]] | None = None
    best_patterns: tuple[int, ...] | None = None
    for small_order in itertools.permutations(range(len(small))):
        ordered_small = [small[i] for i in small_order]
        for complement_order in itertools.permutations(range(len(complements))):
            ordered_complements = [complements[j] for j in complement_order]
            signatures = []
            for x in range(q):
                code = sum(((mask >> x) & 1) << i for i, mask in enumerate(ordered_small))
                code += sum(
                    ((mask >> x) & 1) << (len(ordered_small) + j)
                    for j, mask in enumerate(ordered_complements)
                )
                signatures.append(code)
            ground_order = tuple(sorted(range(q), key=lambda x: (signatures[x], x)))
            candidate = (
                tuple(relabel_mask(mask, ground_order) for mask in ordered_small),
                tuple(relabel_mask(mask, ground_order) for mask in ordered_complements),
            )
            candidate_patterns = tuple(signatures[x] for x in ground_order)
            if best is None or (candidate, candidate_patterns) < (best, best_patterns):
                best = candidate
                best_patterns = candidate_patterns
    assert best is not None and best_patterns is not None
    return {
        "small_masks": list(best[0]),
        "complement_masks": list(best[1]),
        "incidence_pattern_codes": list(best_patterns),
        "incidence_pattern_multiplicities": [
            {"pattern_code": code, "multiplicity": len(list(group))}
            for code, group in itertools.groupby(best_patterns)
        ],
    }


def solve_fixed_split(q: int, a: int, b: int, timeout_ms: int) -> dict[str, Any]:
    """Exact labeled-incidence SMT with safe symmetry breaking."""

    solver = z3.Solver()
    solver.set(timeout=timeout_ms, random_seed=0)
    small = [[z3.Bool(f"s_{q}_{a}_{i}_{x}") for x in range(q)] for i in range(a)]
    complements = [[z3.Bool(f"c_{q}_{a}_{j}_{x}") for x in range(q)] for j in range(b)]

    for row in small:
        solver.add(z3.Sum([z3.If(entry, 1, 0) for entry in row]) >= 2)
    for row in complements:
        solver.add(z3.Sum([z3.If(entry, 1, 0) for entry in row]) >= 4)
    for left, right in itertools.combinations(small, 2):
        solver.add(z3.Or(*(z3.And(x, z3.Not(y)) for x, y in zip(left, right, strict=True))))
        solver.add(z3.Or(*(z3.And(y, z3.Not(x)) for x, y in zip(left, right, strict=True))))
    for left, right in itertools.combinations(complements, 2):
        solver.add(z3.Or(*(z3.And(x, z3.Not(y)) for x, y in zip(left, right, strict=True))))
        solver.add(z3.Or(*(z3.And(y, z3.Not(x)) for x, y in zip(left, right, strict=True))))
    for s_row in small:
        for c_row in complements:
            solver.add(z3.Or(*(z3.And(x, y) for x, y in zip(s_row, c_row, strict=True))))

    # Every R either contains a complete S or is disjoint from a complement C.
    for r_mask in range(1 << q):
        events: list[z3.BoolRef] = []
        events.extend(
            z3.And(*(z3.Not(row[x]) for x in range(q) if not (r_mask >> x & 1)))
            for row in small
        )
        events.extend(
            z3.And(*(z3.Not(row[x]) for x in range(q) if r_mask >> x & 1))
            for row in complements
        )
        solver.add(z3.Or(*events))

    # Safe symmetry removal: order rows by invariant cardinality and columns by
    # their full labeled incidence code.  Neither restriction loses an orbit.
    for rows in (small, complements):
        for left, right in zip(rows, rows[1:], strict=False):
            left_size = z3.Sum([z3.If(x, 1, 0) for x in left])
            right_size = z3.Sum([z3.If(x, 1, 0) for x in right])
            solver.add(left_size <= right_size)
    column_codes = [
        z3.Sum(
            [z3.If(small[i][x], 1 << i, 0) for i in range(a)]
            + [z3.If(complements[j][x], 1 << (a + j), 0) for j in range(b)]
        )
        for x in range(q)
    ]
    for left, right in zip(column_codes, column_codes[1:], strict=False):
        solver.add(left <= right)

    # Exact blocker consequences used only as redundant pruning.
    if (a, b) == (4, 3):
        for left, right in itertools.combinations(small, 2):
            solver.add(z3.And(*(z3.Not(z3.And(x, y)) for x, y in zip(left, right, strict=True))))
    if (a, b) == (5, 2):
        solver.add(
            z3.And(
                *(z3.Not(z3.And(x, y)) for x, y in zip(complements[0], complements[1], strict=True))
            )
        )

    check = solver.check()
    smt_payload: dict[str, Any] = {
        "q": q,
        "a_small": a,
        "b_large_complements": b,
        "timeout_ms": timeout_ms,
        "result": str(check).upper(),
        "canonical_symmetry": "nondecreasing row sizes and full incidence column codes",
        "redundant_blocker_pruning": (a, b) in {(4, 3), (5, 2)},
    }
    if check == z3.sat:
        model = solver.model()
        small_masks = [
            sum((1 << x) for x in range(q) if z3.is_true(model.eval(row[x])))
            for row in small
        ]
        complement_masks = [
            sum((1 << x) for x in range(q) if z3.is_true(model.eval(row[x])))
            for row in complements
        ]
        canonical = canonicalize_witness(q, small_masks, complement_masks)
        canonical_small = canonical["small_masks"]
        canonical_complements = canonical["complement_masks"]
        smt_payload["witness"] = {
            "ground_size": q,
            "small_masks": canonical_small,
            "small_sets": masks_to_sets(canonical_small, q),
            "complement_masks": canonical_complements,
            "complement_sets": masks_to_sets(canonical_complements, q),
            "large_trace_masks": [((1 << q) - 1) ^ mask for mask in canonical_complements],
            "canonicalization": canonical,
            "validator_A": direct_oriented_validator(q, canonical_small, canonical_complements),
            "validator_B": blocker_validator(q, canonical_small, canonical_complements),
        }
        assert smt_payload["witness"]["validator_A"]["accepted"]
        assert smt_payload["witness"]["validator_B"]["accepted"]
    elif check == z3.unknown:
        smt_payload["reason_unknown"] = solver.reason_unknown()
    return smt_payload


def incidence_quotient_audit() -> dict[str, Any]:
    """Finite pattern/multiplicity audit of all a+b=7 blocker splits."""

    split_rows: list[dict[str, Any]] = []
    for a in range(8):
        b = 7 - a
        row: dict[str, Any] = {"a_small": a, "b_complements": b}
        if a == 0:
            row.update(result="ELIMINATED", reason="R=U has no small event")
        elif b == 0:
            row.update(result="ELIMINATED", reason="R=empty has no large event")
        elif b < 2:
            row.update(
                result="ELIMINATED",
                reason="blocker of one complement consists of singletons",
            )
        elif a < 4:
            row.update(
                result="ELIMINATED",
                reason="a-edge clutter has a transversal of size at most a<4",
            )
        elif (a, b) == (4, 3):
            row.update(
                result="ELIMINATED",
                canonical_incidence_patterns=[1, 2, 4, 8],
                multiplicity_variables=["m1", "m2", "m4", "m8"],
                multiplicity_lower_bounds=[2, 2, 2, 2],
                multiplicity_cap=2,
                cap_justification="counts above 2 only increase the product of blocker choices",
                forced_structure="four pairwise-disjoint small edges",
                computed_blocker_count_lower_bound=16,
                required_complement_count=3,
            )
        elif (a, b) == (5, 2):
            row.update(
                result="ELIMINATED",
                canonical_incidence_patterns=[1, 2],
                multiplicity_variables=["m1", "m2"],
                multiplicity_lower_bounds=[4, 4],
                multiplicity_cap=4,
                cap_justification="counts above 4 only increase the product of blocker choices",
                forced_structure="two disjoint complement edges",
                computed_blocker_count_lower_bound=16,
                required_small_count=5,
            )
        else:
            row.update(result="ELIMINATED", reason="already covered by b<2 or a<4 split bounds")
        split_rows.append(row)
    return {
        "epistemic_label": "COMPUTED",
        "quotient_object": "nonzero full membership patterns with integer multiplicities",
        "isolated_zero_pattern": (
            "discarded; it changes neither sizes, antichain witnesses, nor coverage"
        ),
        "blocker_equivalence_used": (
            "small family equals the minimal transversals of the complement family"
        ),
        "splits": split_rows,
        "arbitrary_q_result": "UNSAT_COMPUTED_NO_EXTERNAL_CERTIFICATE",
        "first_unverified_step": (
            "general arbitrary-U blocker/incidence reduction is human-audited code and prose, "
            "not externally certified or formalized"
        ),
    }


def validator_controls() -> dict[str, Any]:
    pairs = [0b00000011, 0b00001100, 0b00110000, 0b11000000]
    complements = [
        sum(1 << choice for choice in choices)
        for choices in itertools.product(*masks_to_sets(pairs, 8))
    ]
    positive_A = direct_oriented_validator(8, pairs, complements, expected_total=None)
    positive_B = blocker_validator(8, pairs, complements, expected_total=None)
    negative_small = pairs[1:]
    negative_A = direct_oriented_validator(8, negative_small, complements, expected_total=None)
    negative_B = blocker_validator(8, negative_small, complements, expected_total=None)
    assert positive_A["accepted"] and positive_B["accepted"]
    assert not negative_A["accepted"] and not negative_B["accepted"]
    return {
        "positive_control": {
            "description": (
                "four disjoint 2-sets and all 16 choice transversals; "
                "total 20, not a seven-member witness"
            ),
            "validator_A": positive_A,
            "validator_B": positive_B,
        },
        "negative_control": {
            "description": "remove one small edge from the positive control",
            "validator_A": negative_A,
            "validator_B": negative_B,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-max", type=int, default=8)
    parser.add_argument("--timeout-ms", type=int, default=60000)
    args = parser.parse_args()
    if not 0 <= args.q_max <= 10:
        raise SystemExit("q-max must lie in [0,10]")
    if not 1 <= args.timeout_ms <= 3_600_000:
        raise SystemExit("timeout-ms must lie in [1,3600000]")

    searches: list[dict[str, Any]] = []
    for q in range(args.q_max + 1):
        for a, b in ((4, 3), (5, 2)):
            searches.append(solve_fixed_split(q, a, b, args.timeout_ms))
    by_q: dict[str, str] = {}
    for q in range(args.q_max + 1):
        rows = [row for row in searches if row["q"] == q]
        if any(row["result"] == "SAT" for row in rows):
            by_q[str(q)] = "SAT"
        elif any(row["result"] == "UNKNOWN" for row in rows):
            by_q[str(q)] = "UNKNOWN"
        else:
            by_q[str(q)] = "UNSAT_COMPUTED"

    payload = {
        "schema": "ai-math-lab.p0054.g4.2-a2-experimentalist.v1",
        "epistemic_label": "COMPUTED",
        "scope_warning": (
            "No UNSAT row is a proof; no external certificate or formal arbitrary-U "
            "reduction is present."
        ),
        "parameters": {
            "q_min": 0,
            "q_max": args.q_max,
            "member_total": 7,
            "solver_timeout_ms_per_split": args.timeout_ms,
            "experiment_random_seed": "NONE",
            "z3_random_seed": 0,
        },
        "versions": {
            "python": platform.python_version(),
            "python_implementation": platform.python_implementation(),
            "z3": z3.get_version_string(),
            "platform": platform.platform(),
        },
        "model": {
            "small_size_min": 2,
            "large_complement_size_min": 4,
            "same_side_antichain": True,
            "cross_condition": "S intersects C",
            "coverage": "for every R: some S subseteq R or some R disjoint from C",
            "exact_split": "a+b=7",
        },
        "structural_split_elimination": incidence_quotient_audit()["splits"],
        "finite_q_results": by_q,
        "finite_q_split_searches": searches,
        "validator_controls": validator_controls(),
        "incidence_quotient": incidence_quotient_audit(),
        "experimental_conclusion": {
            "seven_member_A2": "UNSAT_COMPUTED",
            "first_uncertain_step": (
                "no external certificate and no formal proof of the general quotient reduction"
            ),
            "relation_to_C17": (
                "If independently proved, |A2|>=8 would add one to the C17 layer sum "
                "and support sat(7)>=38; this experiment does not modify or promote C17."
            ),
        },
    }
    json.dump(payload, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
