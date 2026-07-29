from __future__ import annotations

import itertools
import json

import z3  # type: ignore[import-untyped]

import scripts.p0054_layered_sat7 as p0054
import scripts.p0054_verify_candidate as verify_candidate


def _explicit_signature_set(
    signature: p0054.Signature, core_size: int, atom_size: int = 3
) -> frozenset[int]:
    result = {index for index in range(core_size) if signature.core_mask >> index & 1}
    atom = tuple(range(core_size, core_size + atom_size))
    if signature.atom_state == "partial":
        result.add(atom[0])
    elif signature.atom_state == "full":
        result.update(atom)
    return frozenset(result)


def test_symbolic_comparability_matches_explicit_sets() -> None:
    for core_size in range(4):
        for signature, template in itertools.product(
            p0054.all_signatures(core_size), p0054.all_templates(core_size)
        ):
            expanded_signature = _explicit_signature_set(signature, core_size)
            expanded_template = p0054._expand_template(template, core_size, 3)
            expected = (
                expanded_signature < expanded_template or expanded_template < expanded_signature
            )
            assert p0054.signature_strictly_comparable(signature, template) is expected


def test_template_order_matches_explicit_sets() -> None:
    for core_size in range(4):
        for left, right in itertools.product(
            p0054.all_templates(core_size), repeat=2
        ):
            expanded_left = p0054._expand_template(left, core_size, 3)
            expanded_right = p0054._expand_template(right, core_size, 3)
            assert p0054.template_subset(left, right) is (expanded_left <= expanded_right)
            assert p0054.template_strict_subset(left, right) is (expanded_left < expanded_right)


def test_published_56_is_valid_in_both_independent_models() -> None:
    candidate = p0054.published56_candidate()
    assert candidate.total_size == 56
    assert p0054.verify_signature_model(candidate) == {
        "valid": True,
        "verifier": "signature_model",
        "core_size": 7,
        "family_size": 56,
        "layer_sizes": [1, 6, 14, 14, 14, 6, 1],
        "signatures_checked": 2688,
    }
    expanded = p0054.verify_expanded_ground(candidate)
    assert expanded["valid"] is True
    assert expanded["family_size"] == 56
    assert expanded["layer_sizes"] == [1, 6, 14, 14, 14, 6, 1]


def test_published_56_lifts_to_every_larger_core_through_nine() -> None:
    published = p0054.published56_candidate()
    for core_size in (8, 9):
        lifted = p0054.lift_candidate(published, core_size)
        assert lifted.total_size == 56
        assert p0054.verify_signature_model(lifted)["valid"] is True
        assert p0054.verify_expanded_ground(lifted)["valid"] is True


def test_fixed_published_assignment_satisfies_encoding_at_56() -> None:
    candidate = p0054.published56_candidate()
    encoding = p0054.build_encoding(core_size=7, target_size=56, timeout_ms=30_000)
    selected = {
        (layer, template)
        for layer, templates in enumerate(candidate.layers)
        for template in templates
    }
    for key, variable in encoding.variables.items():
        encoding.solver.add(variable == (key in selected))
    assert encoding.solver.check() == z3.sat


def test_tiny_core_cannot_support_seven_disjoint_layers() -> None:
    encoding = p0054.build_encoding(core_size=1, target_size=55, timeout_ms=10_000)
    assert encoding.solver.check() == z3.unsat


def test_cnf_and_z3_agree_on_tiny_core() -> None:
    z3_encoding = p0054.build_encoding(core_size=1, target_size=55, timeout_ms=10_000)
    cnf_encoding = p0054.build_cnf_encoding(core_size=1, target_size=55)
    cnf_solver = z3.Solver()
    variables = {
        index: z3.Bool(f"cnf_{index}")
        for index in range(1, cnf_encoding.cnf.variable_count + 1)
    }
    for clause in cnf_encoding.cnf.clauses:
        cnf_solver.add(
            z3.Or(
                *(variables[abs(literal)] if literal > 0 else z3.Not(variables[-literal])
                  for literal in clause)
            )
        )
    assert (z3_encoding.solver.check() == z3.sat) is (cnf_solver.check() == z3.sat)


def test_fixed_published_assignment_satisfies_cnf_at_56() -> None:
    candidate = p0054.published56_candidate()
    encoding = p0054.build_cnf_encoding(core_size=7, target_size=56)
    selected = {
        (layer, template)
        for layer, templates in enumerate(candidate.layers)
        for template in templates
    }
    solver = z3.Solver()
    variables = {
        index: z3.Bool(f"fixed_cnf_{index}")
        for index in range(1, encoding.cnf.variable_count + 1)
    }
    for clause in encoding.cnf.clauses:
        solver.add(
            z3.Or(
                *(variables[abs(literal)] if literal > 0 else z3.Not(variables[-literal])
                  for literal in clause)
            )
        )
    for key, variable in encoding.variables.items():
        solver.add(variables[variable] == (key in selected))
    assert solver.check() == z3.sat


def test_sequential_counter_is_exact_for_small_inputs() -> None:
    for input_count in range(1, 7):
        for bound in range(input_count + 1):
            cnf = p0054.CnfFormula([])
            next_variable = p0054.add_sequential_at_most(
                cnf, list(range(1, input_count + 1)), bound, input_count + 1
            )
            for bits in itertools.product((False, True), repeat=input_count):
                solver = z3.Solver()
                variables = {
                    index: z3.Bool(f"seq_{input_count}_{bound}_{bits}_{index}")
                    for index in range(1, next_variable)
                }
                for clause in cnf.clauses:
                    solver.add(
                        z3.Or(
                            *(variables[abs(literal)] if literal > 0
                              else z3.Not(variables[-literal]) for literal in clause)
                        )
                    )
                for index, bit in enumerate(bits, start=1):
                    solver.add(variables[index] == bit)
                assert (solver.check() == z3.sat) is (sum(bits) <= bound)


def test_core8_size55_candidate_is_independently_verified() -> None:
    report = verify_candidate.verify_saved_candidate(verify_candidate.DEFAULT_INPUT)
    assert report["mathematical_consequence"] == "EXPLICIT_WITNESS_PROVES_sat7_LE_55"
    assert report["family_size"] == 55
    assert report["layer_sizes"] == [1, 6, 12, 17, 12, 6, 1]
    assert report["family_sha256"] == (
        "8277267a7a9cbc6040432a9d6ffc3f16c540a6013b78bedbd85e6b1e27adde0f"
    )
    assert report["signature_verifier"]["valid"] is True
    assert report["expanded_layer_verifier"]["valid"] is True
    source = json.loads(
        verify_candidate.DEFAULT_INPUT.read_text(encoding="utf-8")
    )
    candidate = verify_candidate.candidate_from_record(source)
    maximal_small_free = verify_candidate.verify_maximal_small_free_certificate(candidate)
    assert maximal_small_free["valid"] is True
    assert maximal_small_free["core_masks_checked_per_layer"] == 256
    assert [
        (layer["small_count"], layer["large_count"])
        for layer in maximal_small_free["layers"]
    ] == [(1, 0), (5, 1), (8, 4), (9, 8), (4, 8), (1, 5), (0, 1)]
    independent = report["independent_saturated_sperner_verifiers"]
    assert independent["agreement"] is True
    assert independent["validator_a"]["valid"] is True
    assert independent["validator_b"]["valid"] is True


def test_verifiers_reject_withdrawn_arxiv_v1_size54_family() -> None:
    """Regression control for the erroneous construction in arXiv:2402.14113v1."""

    def template(text: str) -> p0054.Template:
        return p0054.Template(
            sum(1 << (int(character) - 1) for character in text if character.isdigit()),
            "H" in text,
        )

    def complement(item: p0054.Template) -> p0054.Template:
        return p0054.Template(((1 << 7) - 1) ^ item.core_mask, not item.uses_atom)

    layer1 = tuple(template(text) for text in ("2", "3", "4", "5", "7", "16H"))
    layer2 = tuple(
        template(text)
        for text in (
            "12", "25", "35", "15", "57", "17", "37", "47", "14",
            "136H", "456H", "267H", "234H",
        )
    )
    middle_small = tuple(
        template(text) for text in ("126", "245", "356", "157", "237", "467", "134")
    )
    withdrawn = p0054.Candidate(
        7,
        (
            (template(""),),
            layer1,
            layer2,
            middle_small + tuple(complement(item) for item in middle_small),
            tuple(complement(item) for item in layer2),
            tuple(complement(item) for item in layer1),
            (template("1234567H"),),
        ),
    )
    symbolic = p0054.verify_signature_model(withdrawn)
    expanded = p0054.verify_expanded_ground(withdrawn)
    assert symbolic == {
        "valid": False,
        "failure": "layer_not_saturated",
        "layer": 2,
        "witness": {"core_mask": 38, "atom_state": "empty"},
    }
    assert expanded == {
        "valid": False,
        "failure": "layer_not_saturated",
        "layer": 2,
        "witness": [1, 2, 5],
    }
