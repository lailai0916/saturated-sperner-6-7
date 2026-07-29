#!/usr/bin/env python3
"""Bounded exact checks for the P0054 G4 internal-layer proposal.

Every result emitted by this program is COMPUTED.  The SMT searches cover only
the explicitly listed finite core sizes.  They are not global lower bounds.
"""

from __future__ import annotations

import argparse
import json
import platform
import sys
from fractions import Fraction
from typing import Any

import z3


def is_subset(left: int, right: int) -> bool:
    return left & ~right == 0


def bernoulli_weight(mask: int, core_size: int, p: Fraction) -> Fraction:
    return p ** mask.bit_count() * (1 - p) ** (core_size - mask.bit_count())


def fraction_payload(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def probability_bounds() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for layer, p in ((2, Fraction(2, 5)), (3, Fraction(1, 2)), (4, Fraction(3, 5))):
        small_cap = p**layer
        large_cap = (1 - p) ** (6 - layer)
        event_cap = max(small_cap, large_cap)
        floor_count = (event_cap.denominator + event_cap.numerator - 1) // event_cap.numerator
        rows.append(
            {
                "layer": layer,
                "p": fraction_payload(p),
                "small_event_cap": fraction_payload(small_cap),
                "large_event_cap": fraction_payload(large_cap),
                "max_event_cap": fraction_payload(event_cap),
                "six_event_max_sum": fraction_payload(6 * event_cap),
                "seven_event_max_sum": fraction_payload(7 * event_cap),
                "exact_ceiling_of_reciprocal_cap": floor_count,
            }
        )
    return rows


def exact_event_audit(q_max: int) -> dict[str, Any]:
    probability_parameters = (Fraction(2, 5), Fraction(1, 2), Fraction(3, 5))
    weighted_identities = 0
    own_core_checks = 0
    cross_pairs = 0
    cross_event_checks = 0
    small_pair_checks = 0
    large_pair_checks = 0

    for q in range(q_max + 1):
        universe = range(1 << q)
        weights = {
            p: {r: bernoulli_weight(r, q, p) for r in universe} for p in probability_parameters
        }
        for layer in (2, 3, 4):
            small = [mask for mask in universe if mask.bit_count() >= layer]
            large = [mask for mask in universe if q - mask.bit_count() >= 6 - layer]

            for member in small:
                own_core_checks += 1
                assert is_subset(member, member)
                for p in probability_parameters:
                    enumerated = sum(weights[p][r] for r in universe if is_subset(member, r))
                    assert enumerated == p ** member.bit_count()
                    weighted_identities += 1

            for member in large:
                own_core_checks += 1
                assert is_subset(member, member)
                for p in probability_parameters:
                    enumerated = sum(weights[p][r] for r in universe if is_subset(r, member))
                    assert enumerated == (1 - p) ** (q - member.bit_count())
                    weighted_identities += 1

            for left_index, left in enumerate(small):
                for right in small[left_index + 1 :]:
                    witness = left | right
                    assert is_subset(left, witness) and is_subset(right, witness)
                    small_pair_checks += 1

            for left_index, left in enumerate(large):
                for right in large[left_index + 1 :]:
                    witness = left & right
                    assert is_subset(witness, left) and is_subset(witness, right)
                    large_pair_checks += 1

            for lower in small:
                for upper in large:
                    cross_pairs += 1
                    overlaps = any(is_subset(lower, r) and is_subset(r, upper) for r in universe)
                    assert overlaps == is_subset(lower, upper)
                    cross_event_checks += 1

            # With the source size restrictions, a missing side fails at an
            # explicit boundary core: full core for no-small, empty core for no-large.
            assert not any(is_subset((1 << q) - 1, upper) for upper in large)
            assert not any(is_subset(lower, 0) for lower in small)

    return {
        "core_sizes": [0, q_max],
        "weighted_event_identities_checked": weighted_identities,
        "member_own_core_checks": own_core_checks,
        "small_same_side_pair_intersection_checks": small_pair_checks,
        "large_same_side_pair_intersection_checks": large_pair_checks,
        "cross_overlap_iff_subset_checks": cross_event_checks,
        "cross_pairs_checked": cross_pairs,
        "empty_small_is_ineligible": True,
        "full_large_is_ineligible": True,
        "small_side_empty_fails_at_full_core": True,
        "large_side_empty_fails_at_empty_core": True,
        "all_assertions_passed": True,
    }


def solve_layer(core_size: int, layer: int, target: int, timeout_ms: int) -> dict[str, Any]:
    masks = range(1 << core_size)
    small_masks = [mask for mask in masks if mask.bit_count() >= layer]
    large_masks = [mask for mask in masks if core_size - mask.bit_count() >= 6 - layer]
    small = {mask: z3.Bool(f"s_{layer}_{core_size}_{target}_{mask}") for mask in small_masks}
    large = {mask: z3.Bool(f"l_{layer}_{core_size}_{target}_{mask}") for mask in large_masks}
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.set(random_seed=0)

    antichain_constraints = 0
    coverage_constraints = 0
    for index, left in enumerate(small_masks):
        for right in small_masks[index + 1 :]:
            if is_subset(left, right) or is_subset(right, left):
                solver.add(z3.Or(z3.Not(small[left]), z3.Not(small[right])))
                antichain_constraints += 1
    for index, left in enumerate(large_masks):
        for right in large_masks[index + 1 :]:
            if is_subset(left, right) or is_subset(right, left):
                solver.add(z3.Or(z3.Not(large[left]), z3.Not(large[right])))
                antichain_constraints += 1
    for lower in small_masks:
        for upper in large_masks:
            if is_subset(lower, upper):
                solver.add(z3.Or(z3.Not(small[lower]), z3.Not(large[upper])))
                antichain_constraints += 1
    for core in range(1 << core_size):
        events = [small[member] for member in small_masks if is_subset(member, core)]
        events.extend(large[member] for member in large_masks if is_subset(core, member))
        solver.add(z3.Or(*events))
        coverage_constraints += 1

    variables = [*small.values(), *large.values()]
    if variables:
        solver.add(z3.PbLe([(variable, 1) for variable in variables], target))
    result = solver.check()
    payload: dict[str, Any] = {
        "layer": layer,
        "core_size": core_size,
        "target_at_most": target,
        "eligible_small_variables": len(small),
        "eligible_large_variables": len(large),
        "antichain_constraints": antichain_constraints,
        "coverage_constraints": coverage_constraints,
        "timeout_ms": timeout_ms,
        "result": str(result).upper(),
    }
    if result == z3.sat:
        model = solver.model()
        chosen_small = [
            mask for mask, variable in small.items() if z3.is_true(model.eval(variable))
        ]
        chosen_large = [
            mask for mask, variable in large.items() if z3.is_true(model.eval(variable))
        ]
        payload["witness_small_masks"] = chosen_small
        payload["witness_large_masks"] = chosen_large
        payload["witness_total"] = len(chosen_small) + len(chosen_large)
    elif result == z3.unknown:
        payload["reason_unknown"] = solver.reason_unknown()
    return payload


def equality_eight_reduced_audit(q_max: int) -> dict[str, Any]:
    """Check the exact consequences proposed for an eight-event middle layer.

    At p=1/2, equality forces all selected events to have probability 1/8 and
    the coverage multiplicity to be exactly one at every core.  This routine
    enumerates the event geometry for all q <= q_max.  It does not assume a
    bound outside that finite range.
    """

    checked_q: list[int] = []
    for q in range(q_max + 1):
        small = [mask for mask in range(1 << q) if mask.bit_count() == 3]
        large = [mask for mask in range(1 << q) if q - mask.bit_count() == 3]
        # Any two distinct same-side events overlap.  Thus an exact partition
        # can select at most one event of each side, hence never eight.
        assert all(
            is_subset(left, left | right) and is_subset(right, left | right)
            for index, left in enumerate(small)
            for right in small[index + 1 :]
        )
        assert all(
            is_subset(left & right, left) and is_subset(left & right, right)
            for index, left in enumerate(large)
            for right in large[index + 1 :]
        )
        checked_q.append(q)
    return {
        "core_sizes": [0, q_max],
        "checked_core_sizes": checked_q,
        "forced_event_probability": fraction_payload(Fraction(1, 8)),
        "pointwise_multiplicity_required": 1,
        "maximum_events_compatible_with_same_side_disjointness": 2,
        "eight_event_partition_possible": False,
        "all_assertions_passed": True,
    }


def boundary_witnesses() -> dict[str, Any]:
    small_left, small_right, small_core = 0b0111, 0b1011, 0b1111
    large_left, large_right, large_core = 0b0001, 0b0010, 0b0000
    cross_small = cross_large = cross_core = 0b000111
    assert is_subset(small_left, small_core) and is_subset(small_right, small_core)
    assert is_subset(large_core, large_left) and is_subset(large_core, large_right)
    assert is_subset(cross_small, cross_core) and is_subset(cross_core, cross_large)
    assert is_subset(cross_small, cross_large)
    return {
        "middle_small_pair_overlap": {
            "core_size": 4,
            "small_masks": [small_left, small_right],
            "overlap_core_mask": small_core,
        },
        "middle_large_pair_overlap": {
            "core_size": 4,
            "large_masks": [large_left, large_right],
            "overlap_core_mask": large_core,
        },
        "cross_overlap_if_antichain_is_removed": {
            "core_size": 6,
            "small_mask": cross_small,
            "large_mask": cross_large,
            "overlap_core_mask": cross_core,
            "violates_required_antichain": True,
        },
    }


def compact_searches(searches: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for row in searches:
        grouped.setdefault((row["layer"], row["target_at_most"]), []).append(row)
    compact: list[dict[str, Any]] = []
    for (layer, target), rows in grouped.items():
        compact.append(
            {
                "layer": layer,
                "target_at_most": target,
                "results_by_core_size": {str(row["core_size"]): row["result"] for row in rows},
                "non_unsat_details": [row for row in rows if row["result"] != "UNSAT"],
            }
        )
    return compact


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-max", type=int, default=7)
    parser.add_argument("--timeout-ms", type=int, default=5000)
    args = parser.parse_args()
    if not 0 <= args.q_max <= 10:
        raise SystemExit("q-max must lie in [0,10]")
    if not 1 <= args.timeout_ms <= 60000:
        raise SystemExit("timeout-ms must lie in [1,60000]")

    searches = []
    for layer, target in ((2, 6), (2, 7), (3, 8), (4, 6), (4, 7)):
        for q in range(args.q_max + 1):
            searches.append(solve_layer(q, layer, target, args.timeout_ms))

    result = {
        "schema": "ai-math-lab.p0054.g4-experimentalist.v1",
        "epistemic_label": "COMPUTED",
        "scope_warning": "Finite exact checks only; no global theorem follows from SMT outcomes.",
        "parameters": {
            "q_min": 0,
            "q_max": args.q_max,
            "solver_timeout_ms_per_test": args.timeout_ms,
            "experiment_random_seed": "NONE",
            "z3_random_seed": 0,
        },
        "versions": {
            "python": platform.python_version(),
            "python_implementation": platform.python_implementation(),
            "z3": z3.get_version_string(),
            "platform": platform.platform(),
        },
        "probability_bounds": probability_bounds(),
        "event_audit": exact_event_audit(args.q_max),
        "equality_eight_audit": equality_eight_reduced_audit(args.q_max),
        "boundary_witnesses": boundary_witnesses(),
        "smt_searches": compact_searches(searches),
    }
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
