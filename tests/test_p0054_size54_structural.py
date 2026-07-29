from __future__ import annotations

import itertools

from scripts.p0054_layered_sat7 import (
    Template,
    all_templates,
    template_strict_subset,
    templates_comparable,
)
from scripts.p0054_size54_discovery import is_subset, load_reference_candidate
from scripts.p0054_size54_structural import (
    MIDDLE14_TEMPLATES,
    audit_chain_completion,
    build_rank_window_system_encoding,
    build_single_layer_encoding,
    layer_rank_window,
    template_in_layer_window,
    template_rank,
    verify_single_layer,
)


def _is_saturated_layer(selected: set[Template], core_size: int) -> bool:
    return all(
        not templates_comparable(left, right)
        for left, right in itertools.combinations(selected, 2)
    ) and all(
        any(
            (not template.uses_atom and is_subset(template.core_mask, core_mask))
            or (template.uses_atom and is_subset(core_mask, template.core_mask))
            for template in selected
        )
        for core_mask in range(1 << core_size)
    )


def test_successor_completion_exhaustively_on_two_core_layers() -> None:
    templates = all_templates(2)
    saturated = [
        {template for index, template in enumerate(templates) if bits >> index & 1}
        for bits in range(1 << len(templates))
    ]
    saturated = [layer for layer in saturated if _is_saturated_layer(layer, 2)]
    checked = 0
    for lower in saturated:
        for upper in saturated:
            if lower & upper:
                continue
            if not all(
                any(template_strict_subset(predecessor, item) for predecessor in lower)
                for item in upper
            ):
                continue
            checked += 1
            assert all(
                any(template_strict_subset(item, successor) for successor in upper)
                for item in lower
            )
    assert checked > 0


def test_reference_candidate_has_successors_and_rank_windows() -> None:
    reference = load_reference_candidate()
    audit = audit_chain_completion(reference)
    assert audit["valid"]
    assert audit["layer_sizes"] == [1, 6, 12, 17, 12, 6, 1]
    assert audit["missing_successors"] == []
    assert audit["rank_violations"] == []


def test_eight_core_rank_windows_have_four_ranks() -> None:
    assert [layer_rank_window(8, index) for index in range(7)] == [
        (0, 3),
        (1, 4),
        (2, 5),
        (3, 6),
        (4, 7),
        (5, 8),
        (6, 9),
    ]


def test_rank_window_is_preserved_by_complement_and_layer_reversal() -> None:
    full_mask = (1 << 8) - 1
    for layer_index in range(7):
        for template in all_templates(8):
            dual = Template(full_mask ^ template.core_mask, not template.uses_atom)
            assert template_rank(dual) == 9 - template_rank(template)
            assert template_in_layer_window(template, 8, layer_index) == (
                template_in_layer_window(dual, 8, 6 - layer_index)
            )


def test_single_layer_encoding_primary_counts() -> None:
    counts = [
        build_single_layer_encoding(8, layer_index, 54).primary_variable_count
        for layer_index in range(7)
    ]
    assert counts == [130, 255, 372, 420, 372, 255, 130]
    assert sum(counts) == 1934


def test_single_layer_zero_bound_forces_every_primary_false() -> None:
    encoding = build_single_layer_encoding(8, 0, 0)
    unit_negative = {
        -clause[0] for clause in encoding.cnf.clauses if len(clause) == 1 and clause[0] < 0
    }
    assert unit_negative == set(encoding.variables.values())


def test_middle14_witness_is_a_valid_rank_confined_saturated_layer() -> None:
    audit = verify_single_layer(MIDDLE14_TEMPLATES, 8, 3)
    assert audit == {
        "valid": True,
        "size": 14,
        "small_count": 7,
        "large_count": 7,
        "comparable_pair_count": 0,
        "uncovered_core_masks": [],
        "outside_rank_window_count": 0,
    }


def test_middle14_witness_is_complement_invariant() -> None:
    full_mask = (1 << 8) - 1
    dual = {
        Template(full_mask ^ template.core_mask, not template.uses_atom)
        for template in MIDDLE14_TEMPLATES
    }
    assert dual == set(MIDDLE14_TEMPLATES)


def test_complete_rank_window_encoding_uses_1934_primary_variables() -> None:
    encoding = build_rank_window_system_encoding(
        core_size=8,
        target_size=54,
        layer_upper_bounds=(3, 8, 14, 16, 14, 8, 3),
        small_bound=27,
    )
    assert encoding.primary_variable_count == 1934
    assert encoding.auxiliary_variable_count > 0
    assert encoding.layer_upper_bounds == (3, 8, 14, 16, 14, 8, 3)


def test_fixed_middle14_adds_one_unit_clause_per_middle_variable() -> None:
    unfixed = build_rank_window_system_encoding(
        core_size=8,
        target_size=54,
        layer_upper_bounds=(3, 8, 14, 16, 14, 8, 3),
        small_bound=27,
    )
    fixed = build_rank_window_system_encoding(
        core_size=8,
        target_size=54,
        layer_upper_bounds=(3, 8, 14, 16, 14, 8, 3),
        small_bound=27,
        fixed_layers={3: MIDDLE14_TEMPLATES},
    )
    assert len(fixed.cnf.clauses) - len(unfixed.cnf.clauses) == 420
