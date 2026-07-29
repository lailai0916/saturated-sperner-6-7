from __future__ import annotations

import itertools

from scripts.p0054_layered_sat7 import (
    Template,
    all_signatures,
    all_templates,
    build_cnf_encoding,
    build_encoding,
    signature_exact_template,
    signature_strictly_comparable,
    templates_comparable,
)
from scripts.p0054_size54_discovery import (
    KISSAT_PORTFOLIO,
    PORTFOLIO,
    build_oriented_cnf_encoding,
    dual_candidate,
    is_subset,
    load_reference_candidate,
    reference_variables,
    validate_candidate,
)


def test_reference_candidate_and_variables_are_frozen_size55() -> None:
    reference = load_reference_candidate()
    encoding = build_encoding(core_size=8, target_size=55, timeout_ms=1_000)
    variables = reference_variables(encoding.variables, reference)
    assert reference.total_size == 55
    assert len(variables) == 55
    assert len(set(map(str, variables))) == 55


def test_reference_templates_are_all_in_the_complete_encoding() -> None:
    reference = load_reference_candidate()
    complete = {
        (layer_index, template)
        for layer_index in range(7)
        for template in (
            Template(mask, uses_atom) for uses_atom in (False, True) for mask in range(1 << 8)
        )
    }
    assert all(
        (layer_index, template) in complete
        for layer_index, layer in enumerate(reference.layers)
        for template in layer
    )


def test_duality_reorients_reference_to_27_small_members() -> None:
    reference = load_reference_candidate()
    dual = dual_candidate(reference)
    round_trip = dual_candidate(dual)
    assert all(
        set(round_trip_layer) == set(reference_layer)
        for round_trip_layer, reference_layer in zip(
            round_trip.layers, reference.layers, strict=True
        )
    )
    assert sum(
        not template.uses_atom for layer in dual.layers for template in layer
    ) == 27
    assert dual.total_size == 55


def test_all_portfolio_configurations_have_distinct_names() -> None:
    assert len({configuration.name for configuration in PORTFOLIO}) == len(PORTFOLIO)
    assert len({configuration.name for configuration in KISSAT_PORTFOLIO}) == len(KISSAT_PORTFOLIO)


def test_validator_rejects_size55_for_size54_gate() -> None:
    reference = load_reference_candidate()
    try:
        validate_candidate(reference)
    except AssertionError:
        pass
    else:
        raise AssertionError("size-54 gate accepted the size-55 reference")


def test_oriented_layer_condition_matches_all_signatures_on_core2() -> None:
    templates = all_templates(2)
    for selected_bits in range(1 << len(templates)):
        selected = {
            template for index, template in enumerate(templates) if selected_bits >> index & 1
        }
        antichain = all(
            not templates_comparable(left, right)
            for left, right in itertools.combinations(selected, 2)
        )
        signature_condition = antichain and all(
            signature_exact_template(signature) in selected
            or any(signature_strictly_comparable(signature, template) for template in selected)
            for signature in all_signatures(2)
        )
        oriented_condition = antichain and all(
            any(
                not template.uses_atom and is_subset(template.core_mask, core_mask)
                for template in selected
            )
            or any(
                template.uses_atom and is_subset(core_mask, template.core_mask)
                for template in selected
            )
            for core_mask in range(1 << 2)
        )
        assert oriented_condition == signature_condition


def test_oriented_encoding_has_fewer_structural_clauses_on_core2() -> None:
    oriented = build_oriented_cnf_encoding(core_size=2, target_size=54, small_bound=None)
    baseline = build_cnf_encoding(core_size=2, target_size=54)
    assert len(oriented.cnf.clauses) < len(baseline.cnf.clauses)
