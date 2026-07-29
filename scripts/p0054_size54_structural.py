"""Certificate-oriented structural lower bounds for the P0054 size-54 gate.

The seven P0054 layers are not independent arbitrary saturated antichains.
Saturation, disjointness, and the stated predecessor condition force every
member of every nonfinal layer to have a strict successor.  Consequently each
member lies on a strict seven-template chain.  For an eight-element core this
confines layer ``i`` to template ranks ``i`` through ``i + 3``.

This module builds one exact CNF for each rank-confined layer.  A checked UNSAT
certificate for the bounds ``0, 5, 11, 13`` on layers ``0, 1, 2, 3`` proves
the lower bounds ``1, 6, 12, 14``.  Complement duality supplies the remaining
three bounds.  Solver output is not promoted to a theorem until DRAT-trim has
accepted every proof file.  A separately verified 14-member middle-layer
witness shows that the middle bound is sharp.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import time
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from scripts.p0054_layered_sat7 import (
    Candidate,
    CnfFormula,
    Template,
    add_sequential_at_most,
    all_templates,
    template_strict_subset,
    templates_comparable,
    verify_signature_model,
)
from scripts.p0054_size54_discovery import (
    REFERENCE_PATH,
    is_subset,
    load_reference_candidate,
    sha256_file,
)

LAYER_COUNT = 7
CORE_SIZE = 8
LOWER_BOUND_CERTIFICATES = ((0, 0), (1, 5), (2, 11), (3, 13))
DEFAULT_OUTPUT_DIRECTORY = Path("Problems/P0054/experiments/size54-g3-layer-bounds")
MIDDLE14_TEMPLATES = (
    Template(14, False),
    Template(52, False),
    Template(88, False),
    Template(98, False),
    Template(146, False),
    Template(168, False),
    Template(196, False),
    Template(59, True),
    Template(87, True),
    Template(109, True),
    Template(157, True),
    Template(167, True),
    Template(203, True),
    Template(241, True),
)


@dataclass(frozen=True)
class SingleLayerEncoding:
    """One exact rank-window layer CNF."""

    layer_index: int
    size_bound: int
    cnf: CnfFormula
    variables: dict[Template, int]
    eligible_templates: tuple[Template, ...]
    primary_variable_count: int
    auxiliary_variable_count: int


@dataclass(frozen=True)
class RankWindowSystemEncoding:
    """The complete seven-layer encoding after the proved rank reduction."""

    cnf: CnfFormula
    variables: dict[tuple[int, Template], int]
    primary_variable_count: int
    auxiliary_variable_count: int
    layer_upper_bounds: tuple[int, ...]


def template_rank(template: Template) -> int:
    """Rank in the template Boolean lattice, treating ``H`` as one atom."""

    return template.core_mask.bit_count() + int(template.uses_atom)


def layer_rank_window(core_size: int, layer_index: int) -> tuple[int, int]:
    """Return the ranks available to a member of a full seven-layer chain."""

    if core_size < 0:
        raise ValueError("core_size must be nonnegative")
    if not 0 <= layer_index < LAYER_COUNT:
        raise ValueError("layer_index must lie in 0..6")
    return layer_index, core_size + 1 - (LAYER_COUNT - 1 - layer_index)


def template_in_layer_window(
    template: Template, core_size: int, layer_index: int
) -> bool:
    """Return whether a template can occur in the specified layer."""

    lower, upper = layer_rank_window(core_size, layer_index)
    return lower <= template_rank(template) <= upper


def audit_chain_completion(candidate: Candidate) -> dict[str, Any]:
    """Check successor completion and the induced rank windows on a candidate."""

    signature = verify_signature_model(candidate)
    if not signature["valid"]:
        raise AssertionError(signature)
    missing_successors: list[dict[str, Any]] = []
    for layer_index in range(LAYER_COUNT - 1):
        upper_layer = candidate.layers[layer_index + 1]
        for lower in candidate.layers[layer_index]:
            if not any(template_strict_subset(lower, upper) for upper in upper_layer):
                missing_successors.append(
                    {
                        "layer_index": layer_index,
                        "core_mask": lower.core_mask,
                        "uses_atom": lower.uses_atom,
                    }
                )
    rank_violations = [
        {
            "layer_index": layer_index,
            "core_mask": template.core_mask,
            "uses_atom": template.uses_atom,
            "rank": template_rank(template),
            "window": list(layer_rank_window(candidate.core_size, layer_index)),
        }
        for layer_index, layer in enumerate(candidate.layers)
        for template in layer
        if not template_in_layer_window(template, candidate.core_size, layer_index)
    ]
    return {
        "valid": not missing_successors and not rank_violations,
        "family_size": candidate.total_size,
        "layer_sizes": [len(layer) for layer in candidate.layers],
        "missing_successors": missing_successors,
        "rank_violations": rank_violations,
    }


def build_single_layer_encoding(
    core_size: int, layer_index: int, size_bound: int
) -> SingleLayerEncoding:
    """Build the exact antichain-and-oriented-coverage CNF in one rank window."""

    if size_bound < 0:
        raise ValueError("size_bound must be nonnegative")
    eligible = tuple(
        template
        for template in all_templates(core_size)
        if template_in_layer_window(template, core_size, layer_index)
    )
    variables = {template: index + 1 for index, template in enumerate(eligible)}
    cnf = CnfFormula([])

    for left, right in itertools.combinations(eligible, 2):
        if templates_comparable(left, right):
            cnf.append([-variables[left], -variables[right]])

    for core_mask in range(1 << core_size):
        witnesses = [
            variables[template]
            for template in eligible
            if (
                not template.uses_atom
                and is_subset(template.core_mask, core_mask)
            )
            or (
                template.uses_atom
                and is_subset(core_mask, template.core_mask)
            )
        ]
        cnf.append(witnesses)

    next_variable = add_sequential_at_most(
        cnf,
        list(variables.values()),
        size_bound,
        len(variables) + 1,
    )
    return SingleLayerEncoding(
        layer_index=layer_index,
        size_bound=size_bound,
        cnf=cnf,
        variables=variables,
        eligible_templates=eligible,
        primary_variable_count=len(variables),
        auxiliary_variable_count=next_variable - len(variables) - 1,
    )


def verify_single_layer(
    templates: tuple[Template, ...], core_size: int, layer_index: int
) -> dict[str, Any]:
    """Independently check antichain, coverage, and rank-window conditions."""

    comparable_pairs = [
        (left, right)
        for left, right in itertools.combinations(templates, 2)
        if templates_comparable(left, right)
    ]
    uncovered_masks = [
        core_mask
        for core_mask in range(1 << core_size)
        if not any(
            (
                not template.uses_atom
                and is_subset(template.core_mask, core_mask)
            )
            or (
                template.uses_atom
                and is_subset(core_mask, template.core_mask)
            )
            for template in templates
        )
    ]
    outside_window = [
        template
        for template in templates
        if not template_in_layer_window(template, core_size, layer_index)
    ]
    return {
        "valid": not comparable_pairs and not uncovered_masks and not outside_window,
        "size": len(templates),
        "small_count": sum(not template.uses_atom for template in templates),
        "large_count": sum(template.uses_atom for template in templates),
        "comparable_pair_count": len(comparable_pairs),
        "uncovered_core_masks": uncovered_masks,
        "outside_rank_window_count": len(outside_window),
    }


def build_rank_window_system_encoding(
    core_size: int,
    target_size: int,
    layer_upper_bounds: tuple[int, ...],
    small_bound: int | None,
    fixed_layers: dict[int, tuple[Template, ...]] | None = None,
) -> RankWindowSystemEncoding:
    """Build the complete reduced seven-layer decision CNF.

    The rank windows and successor implications are consequences of the
    original P0054 hypotheses.  The caller may add independently proved layer
    upper bounds; for target 54 the certified minima permit ``m_i + 2``.
    """

    if core_size < 0:
        raise ValueError("core_size must be nonnegative")
    if target_size < 0:
        raise ValueError("target_size must be nonnegative")
    if len(layer_upper_bounds) != LAYER_COUNT:
        raise ValueError("one upper bound is required for each layer")
    if any(bound < 0 for bound in layer_upper_bounds):
        raise ValueError("layer upper bounds must be nonnegative")
    if small_bound is not None and small_bound < 0:
        raise ValueError("small_bound must be nonnegative")
    fixed_layers = fixed_layers or {}
    if any(not 0 <= index < LAYER_COUNT for index in fixed_layers):
        raise ValueError("fixed layer index must lie in 0..6")

    all_core_templates = all_templates(core_size)
    eligible_by_layer = tuple(
        tuple(
            template
            for template in all_core_templates
            if template_in_layer_window(template, core_size, layer_index)
        )
        for layer_index in range(LAYER_COUNT)
    )
    variables: dict[tuple[int, Template], int] = {}
    next_variable = 1
    for layer_index, eligible in enumerate(eligible_by_layer):
        for template in eligible:
            variables[layer_index, template] = next_variable
            next_variable += 1
    primary_count = next_variable - 1
    cnf = CnfFormula([])

    for layer_index, eligible in enumerate(eligible_by_layer):
        for left, right in itertools.combinations(eligible, 2):
            if templates_comparable(left, right):
                cnf.append(
                    [
                        -variables[layer_index, left],
                        -variables[layer_index, right],
                    ]
                )
        for core_mask in range(1 << core_size):
            witnesses = [
                variables[layer_index, template]
                for template in eligible
                if (
                    not template.uses_atom
                    and is_subset(template.core_mask, core_mask)
                )
                or (
                    template.uses_atom
                    and is_subset(core_mask, template.core_mask)
                )
            ]
            cnf.append(witnesses)

    for template in all_core_templates:
        occurrences = [
            variables[layer_index, template]
            for layer_index in range(LAYER_COUNT)
            if (layer_index, template) in variables
        ]
        for left_occurrence, right_occurrence in itertools.combinations(occurrences, 2):
            cnf.append([-left_occurrence, -right_occurrence])

    for layer_index in range(1, LAYER_COUNT):
        lower_layer = eligible_by_layer[layer_index - 1]
        upper_layer = eligible_by_layer[layer_index]
        for upper in upper_layer:
            predecessors = [
                variables[layer_index - 1, lower]
                for lower in lower_layer
                if template_strict_subset(lower, upper)
            ]
            cnf.append([-variables[layer_index, upper], *predecessors])
        for lower in lower_layer:
            successors = [
                variables[layer_index, upper]
                for upper in upper_layer
                if template_strict_subset(lower, upper)
            ]
            cnf.append([-variables[layer_index - 1, lower], *successors])

    for layer_index, selected in fixed_layers.items():
        selected_set = set(selected)
        eligible_set = set(eligible_by_layer[layer_index])
        if not selected_set <= eligible_set:
            raise ValueError("fixed layer contains a template outside its rank window")
        for template in eligible_by_layer[layer_index]:
            variable = variables[layer_index, template]
            cnf.append([variable if template in selected_set else -variable])

    primary_literals = list(variables.values())
    next_variable = add_sequential_at_most(
        cnf, primary_literals, target_size, primary_count + 1
    )
    if small_bound is not None:
        small_literals = [
            variable
            for (layer_index, template), variable in variables.items()
            if not template.uses_atom and 0 <= layer_index < LAYER_COUNT
        ]
        next_variable = add_sequential_at_most(
            cnf, small_literals, small_bound, next_variable
        )
    for layer_index, upper_bound in enumerate(layer_upper_bounds):
        layer_literals = [
            variables[layer_index, template]
            for template in eligible_by_layer[layer_index]
        ]
        next_variable = add_sequential_at_most(
            cnf, layer_literals, upper_bound, next_variable
        )
    return RankWindowSystemEncoding(
        cnf=cnf,
        variables=variables,
        primary_variable_count=primary_count,
        auxiliary_variable_count=next_variable - primary_count - 1,
        layer_upper_bounds=layer_upper_bounds,
    )


def decode_rank_window_model(
    encoding: RankWindowSystemEncoding, core_size: int, signed_model: list[int]
) -> Candidate:
    """Decode the sparse primary-variable portion of a SAT model."""

    positive = {literal for literal in signed_model if literal > 0}
    return Candidate(
        core_size,
        tuple(
            tuple(
                sorted(
                    template
                    for (candidate_layer, template), variable in encoding.variables.items()
                    if candidate_layer == layer_index and variable in positive
                )
            )
            for layer_index in range(LAYER_COUNT)
        ),
    )


def checker_commit(checker: Path) -> str | None:
    """Return the checker repository commit when available."""

    completed = subprocess.run(
        ["git", "-C", str(checker.parent), "rev-parse", "HEAD"],
        check=False,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip() if completed.returncode == 0 else None


def _run_one_certificate(
    layer_index: int,
    size_bound: int,
    output_directory: Path,
    solver: Path,
    checker: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    """Generate and independently check one single-layer UNSAT certificate."""

    encoding = build_single_layer_encoding(CORE_SIZE, layer_index, size_bound)
    stem = f"core8-layer{layer_index}-at-most-{size_bound}"
    cnf_path = output_directory / f"{stem}.cnf"
    proof_path = output_directory / f"{stem}.drat"
    solver_log = output_directory / f"{stem}.kissat.log"
    checker_log = output_directory / f"{stem}.drat-trim.log"
    encoding.cnf.to_file(cnf_path)

    command = [
        str(solver),
        f"--time={timeout_seconds}",
        str(cnf_path),
        str(proof_path),
    ]
    started = time.perf_counter()
    completed = subprocess.run(command, check=False, capture_output=True, text=True)
    runtime_seconds = time.perf_counter() - started
    combined = completed.stdout + completed.stderr
    solver_log.write_text(combined, encoding="utf-8")
    if completed.returncode != 20 or "s UNSATISFIABLE" not in combined:
        return {
            "layer_index": layer_index,
            "size_bound": size_bound,
            "solver_result": "UNKNOWN_OR_TIMEOUT",
            "epistemic_label": "COMPUTED",
            "runtime_seconds": runtime_seconds,
            "cnf_path": str(cnf_path),
            "cnf_sha256": sha256_file(cnf_path),
            "solver_log": str(solver_log),
            "solver_log_sha256": sha256_file(solver_log),
        }
    if not proof_path.is_file() or proof_path.stat().st_size == 0:
        raise AssertionError("UNSAT solver run did not produce a DRAT proof")

    checked = subprocess.run(
        [str(checker), str(cnf_path), str(proof_path)],
        check=False,
        capture_output=True,
        text=True,
    )
    checked_output = checked.stdout + checked.stderr
    checker_log.write_text(checked_output, encoding="utf-8")
    if checked.returncode != 0 or "s VERIFIED" not in checked_output:
        raise RuntimeError(f"DRAT verification failed for layer {layer_index}")
    return {
        "layer_index": layer_index,
        "rank_window": list(layer_rank_window(CORE_SIZE, layer_index)),
        "size_bound": size_bound,
        "proved_minimum_at_least": size_bound + 1,
        "solver_result": "UNSAT",
        "checker_result": "VERIFIED",
        "epistemic_label": "PROVED_WITH_CHECKED_CERTIFICATE",
        "runtime_seconds": runtime_seconds,
        "primary_variable_count": encoding.primary_variable_count,
        "auxiliary_variable_count": encoding.auxiliary_variable_count,
        "clause_count": len(encoding.cnf.clauses),
        "cnf_path": str(cnf_path),
        "cnf_bytes": cnf_path.stat().st_size,
        "cnf_sha256": sha256_file(cnf_path),
        "proof_path": str(proof_path),
        "proof_bytes": proof_path.stat().st_size,
        "proof_sha256": sha256_file(proof_path),
        "solver_log": str(solver_log),
        "solver_log_sha256": sha256_file(solver_log),
        "checker_log": str(checker_log),
        "checker_log_sha256": sha256_file(checker_log),
    }


def certify_layer_bounds(
    output_directory: Path,
    solver: Path,
    checker: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    """Run the four independent layer lower-bound certificates."""

    if timeout_seconds <= 0:
        raise ValueError("timeout_seconds must be positive")
    if not solver.is_file():
        raise FileNotFoundError(solver)
    if not checker.is_file():
        raise FileNotFoundError(checker)
    output_directory.mkdir(parents=True, exist_ok=True)
    reference = load_reference_candidate()
    reference_audit = audit_chain_completion(reference)
    if not reference_audit["valid"]:
        raise AssertionError(reference_audit)
    middle14_audit = verify_single_layer(MIDDLE14_TEMPLATES, CORE_SIZE, 3)
    if not middle14_audit["valid"]:
        raise AssertionError(middle14_audit)

    records = [
        _run_one_certificate(
            layer_index,
            size_bound,
            output_directory,
            solver,
            checker,
            timeout_seconds,
        )
        for layer_index, size_bound in LOWER_BOUND_CERTIFICATES
    ]
    all_verified = all(record.get("checker_result") == "VERIFIED" for record in records)
    semantic = {
        "core_size": CORE_SIZE,
        "layer_count": LAYER_COUNT,
        "reference_path": str(REFERENCE_PATH),
        "reference_sha256": sha256_file(REFERENCE_PATH),
        "reference_audit": reference_audit,
        "middle14_witness": [
            {
                "core_mask": template.core_mask,
                "uses_atom": template.uses_atom,
                "rank": template_rank(template),
            }
            for template in MIDDLE14_TEMPLATES
        ],
        "middle14_audit": middle14_audit,
        "solver": str(solver),
        "solver_sha256": sha256_file(solver),
        "checker": str(checker),
        "checker_sha256": sha256_file(checker),
        "checker_commit": checker_commit(checker),
        "records": records,
        "all_certificates_verified": all_verified,
        "proved_layer_minima_if_verified": [1, 6, 12, 14, 12, 6, 1],
        "proved_total_independent_layer_lower_bound_if_verified": 52,
    }
    canonical = json.dumps(semantic, sort_keys=True, separators=(",", ":"))
    report = {
        "schema": "ai-math-lab.p0054.size54-layer-bounds.v1",
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "run_mode": "STRUCTURAL_LOWER_BOUND_CERTIFICATION",
        "epistemic_label": "PROVED" if all_verified else "COMPUTED",
        "global_sat7_lower_bound_claimed": False,
        "semantic": semantic,
        "semantic_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
    }
    report_path = output_directory / "verification-manifest.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=1800)
    parser.add_argument("--output-directory", type=Path, default=DEFAULT_OUTPUT_DIRECTORY)
    return parser.parse_args()


def main() -> None:
    """Generate, solve, verify, and record the layer-bound certificates."""

    args = parse_args()
    report = certify_layer_bounds(
        args.output_directory,
        args.solver,
        args.checker,
        args.timeout_seconds,
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
