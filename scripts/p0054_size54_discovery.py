"""Bounded discovery search for a 54-member P0054 construction.

This module searches only the eight-core, one-common-block, seven-layer
template class defined in ``Problems/P0054/statement.md``.  It has two modes:

* ``neighborhood`` asks Z3 for a target-54 candidate that retains many members
  of the frozen size-55 construction; and
* ``portfolio`` runs several CaDiCaL configurations on the complete target-54
  CNF with no neighborhood restriction.

Every negative or timed-out result is labelled ``COMPUTED`` and is not a lower
bound.  A positive result is accepted only after the symbolic layer verifier,
the expanded-ground layer verifier, and both independent union-level
verifiers accept the extracted family.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import subprocess
import time
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

import z3  # type: ignore[import-untyped]

from scripts.p0053_sat7 import dual_verify, family_sha256
from scripts.p0054_layered_sat7 import (
    Candidate,
    CnfEncoding,
    CnfFormula,
    Template,
    _candidate_from_signed_model,
    _candidate_semantic,
    _semantic_hash,
    add_sequential_at_most,
    all_templates,
    build_cnf_encoding,
    build_encoding,
    template_strict_subset,
    verify_expanded_ground,
    verify_signature_model,
)
from scripts.p0054_verify_candidate import candidate_from_record, expanded_family

REFERENCE_PATH = Path("Problems/P0054/experiments/certificates/core-8-target-55-selfcontained.json")
DEFAULT_OUTPUT_DIRECTORY = Path("Problems/P0054/experiments/size54-g2")


@dataclass(frozen=True)
class SolverConfiguration:
    """One deterministic CaDiCaL command-line configuration."""

    name: str
    options: tuple[str, ...]


PORTFOLIO = (
    SolverConfiguration("default", ("--default",)),
    SolverConfiguration("sat", ("--sat",)),
    SolverConfiguration(
        "sat-shuffle-seed1",
        ("--sat", "--seed=1", "--shuffle=true", "--randec=true"),
    ),
    SolverConfiguration(
        "sat-shuffle-seed2",
        ("--sat", "--seed=2", "--shuffle=true", "--reverse=true"),
    ),
)

KISSAT_PORTFOLIO = (
    SolverConfiguration("default", ("--default",)),
    SolverConfiguration("sat", ("--sat",)),
    SolverConfiguration("sat-seed1", ("--sat", "--seed=1")),
    SolverConfiguration("sat-seed2-negative-phase", ("--sat", "--seed=2", "--phase=false")),
)


def sha256_file(path: Path) -> str:
    """Return the SHA-256 digest of a file without loading it at once."""

    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_reference_candidate(path: Path = REFERENCE_PATH) -> Candidate:
    """Load and hash-check the frozen size-55 candidate."""

    payload = json.loads(path.read_text(encoding="utf-8"))
    candidate = candidate_from_record(payload)
    if candidate.core_size != 8 or candidate.total_size != 55:
        raise AssertionError("reference candidate is not the frozen eight-core size-55 family")
    return candidate


def dual_candidate(candidate: Candidate) -> Candidate:
    """Complement every template and reverse the layer order."""

    full_mask = (1 << candidate.core_size) - 1
    return Candidate(
        candidate.core_size,
        tuple(
            tuple(
                sorted(
                    Template(full_mask ^ template.core_mask, not template.uses_atom)
                    for template in candidate.layers[6 - layer_index]
                )
            )
            for layer_index in range(7)
        ),
    )


def reference_variables(
    variables: dict[tuple[int, Template], Any], reference: Candidate
) -> tuple[Any, ...]:
    """Return variables corresponding to the frozen candidate's members."""

    return tuple(
        variables[layer_index, template]
        for layer_index, layer in enumerate(reference.layers)
        for template in layer
    )


def is_subset(left: int, right: int) -> bool:
    """Return whether one core mask is a subset of another."""

    return left & right == left


def build_oriented_cnf_encoding(
    core_size: int, target_size: int, small_bound: int | None
) -> CnfEncoding:
    """Build an exact CNF using one oriented saturation clause per core mask.

    For a layer with small templates ``S`` and large templates ``L ∪ H``, a
    subset whose core mask is ``R`` is covered exactly when some selected small
    core lies below ``R`` or some selected large core lies above ``R``.  The
    nonempty proper atom state shows that this condition is also necessary.

    The optional bound ``small_bound=27`` is a safe duality breaker at target
    54: complementing every set and reversing the seven layers exchanges the
    total number of small and large templates, so one orientation of every
    candidate with at most 54 members has at most 27 small templates.
    """

    if core_size < 0:
        raise ValueError("core_size must be nonnegative")
    if target_size < 0:
        raise ValueError("target_size must be nonnegative")
    if small_bound is not None and small_bound < 0:
        raise ValueError("small_bound must be nonnegative")

    cnf = CnfFormula([])
    templates = all_templates(core_size)
    small = tuple(template for template in templates if not template.uses_atom)
    large = tuple(template for template in templates if template.uses_atom)
    variables: dict[tuple[int, Template], int] = {}
    next_variable = 1
    for layer in range(7):
        for template in templates:
            variables[layer, template] = next_variable
            next_variable += 1
    primary_count = next_variable - 1

    for layer in range(7):
        for index, left in enumerate(small):
            for right in small[index + 1 :]:
                if is_subset(left.core_mask, right.core_mask) or is_subset(
                    right.core_mask, left.core_mask
                ):
                    cnf.append([-variables[layer, left], -variables[layer, right]])
        for index, left in enumerate(large):
            for right in large[index + 1 :]:
                if is_subset(left.core_mask, right.core_mask) or is_subset(
                    right.core_mask, left.core_mask
                ):
                    cnf.append([-variables[layer, left], -variables[layer, right]])
        for small_template in small:
            for large_template in large:
                if is_subset(small_template.core_mask, large_template.core_mask):
                    cnf.append(
                        [
                            -variables[layer, small_template],
                            -variables[layer, large_template],
                        ]
                    )

        for core_mask in range(1 << core_size):
            witnesses = [
                variables[layer, template]
                for template in small
                if is_subset(template.core_mask, core_mask)
            ]
            witnesses.extend(
                variables[layer, template]
                for template in large
                if is_subset(core_mask, template.core_mask)
            )
            cnf.append(witnesses)

    for template in templates:
        for left_layer in range(7):
            for right_layer in range(left_layer + 1, 7):
                cnf.append(
                    [
                        -variables[left_layer, template],
                        -variables[right_layer, template],
                    ]
                )

    for layer in range(1, 7):
        for upper in small:
            predecessors = [
                variables[layer - 1, lower]
                for lower in small
                if template_strict_subset(lower, upper)
            ]
            cnf.append([-variables[layer, upper], *predecessors])
        for upper in large:
            predecessors = [
                variables[layer - 1, lower]
                for lower in templates
                if template_strict_subset(lower, upper)
            ]
            cnf.append([-variables[layer, upper], *predecessors])

    primary_literals = [variables[layer, template] for layer in range(7) for template in templates]
    next_variable = add_sequential_at_most(cnf, primary_literals, target_size, primary_count + 1)
    if small_bound is not None:
        small_literals = [variables[layer, template] for layer in range(7) for template in small]
        next_variable = add_sequential_at_most(cnf, small_literals, small_bound, next_variable)
    return CnfEncoding(
        cnf=cnf,
        variables=variables,
        templates=templates,
        primary_variable_count=primary_count,
        auxiliary_variable_count=next_variable - primary_count - 1,
    )


def validate_candidate(candidate: Candidate) -> dict[str, Any]:
    """Apply all four exact semantic checks to a discovered candidate."""

    signature = verify_signature_model(candidate)
    expanded = verify_expanded_ground(candidate, atom_size=3)
    family = expanded_family(candidate, atom_size=3)
    dual = dual_verify(candidate.core_size + 3, 7, family)
    valid = bool(
        candidate.total_size <= 54
        and len(set(family)) == candidate.total_size
        and signature["valid"]
        and expanded["valid"]
        and dual["validator_a"]["valid"]
        and dual["validator_b"]["valid"]
        and dual["agreement"]
    )
    if not valid:
        raise AssertionError(
            {
                "candidate_size": candidate.total_size,
                "signature": signature,
                "expanded": expanded,
                "dual": dual,
            }
        )
    return {
        "valid": True,
        "candidate_sha256": _semantic_hash(_candidate_semantic(candidate)),
        "expanded_family_sha256": family_sha256(candidate.core_size + 3, 7, family),
        "family_size": candidate.total_size,
        "layer_sizes": [len(layer) for layer in candidate.layers],
        "signature_verifier": signature,
        "expanded_verifier": expanded,
        "union_verifier_a": {
            key: value for key, value in dual["validator_a"].items() if key != "runtime_seconds"
        },
        "union_verifier_b": {
            key: value for key, value in dual["validator_b"].items() if key != "runtime_seconds"
        },
    }


def run_neighborhood_search(
    reference_path: Path,
    output_path: Path,
    minimum_overlaps: tuple[int, ...],
    timeout_seconds: float,
) -> dict[str, Any]:
    """Search successively wider Hamming neighborhoods of the size-55 family."""

    if timeout_seconds <= 0:
        raise ValueError("timeout_seconds must be positive")
    reference = load_reference_candidate(reference_path)
    runs: list[dict[str, Any]] = []
    discovered: Candidate | None = None

    for minimum_overlap in minimum_overlaps:
        if not 0 <= minimum_overlap <= reference.total_size:
            raise ValueError("minimum overlap is outside the reference family")
        encoding = build_encoding(
            core_size=reference.core_size,
            target_size=54,
            timeout_ms=max(1, round(timeout_seconds * 1000)),
        )
        overlap_variables = reference_variables(encoding.variables, reference)
        encoding.solver.add(
            z3.PbGe([(variable, 1) for variable in overlap_variables], minimum_overlap)
        )

        started = time.perf_counter()
        result = encoding.solver.check()
        runtime = time.perf_counter() - started
        record: dict[str, Any] = {
            "minimum_overlap": minimum_overlap,
            "maximum_reference_deletions": reference.total_size - minimum_overlap,
            "target_size": 54,
            "timeout_seconds": timeout_seconds,
            "runtime_seconds": runtime,
            "solver_result": str(result).upper(),
            "epistemic_label": "COMPUTED",
        }
        if result == z3.sat:
            model = encoding.solver.model()
            candidate = Candidate(
                reference.core_size,
                tuple(
                    tuple(
                        template
                        for template in encoding.templates
                        if z3.is_true(
                            model.eval(
                                encoding.variables[layer, template],
                                model_completion=True,
                            )
                        )
                    )
                    for layer in range(7)
                ),
            )
            verification = validate_candidate(candidate)
            actual_overlap = sum(
                template in set(candidate.layers[layer_index])
                for layer_index, layer in enumerate(reference.layers)
                for template in layer
            )
            record.update(
                {
                    "candidate": _candidate_semantic(candidate),
                    "actual_overlap": actual_overlap,
                    "verification": verification,
                }
            )
            discovered = candidate
        elif result == z3.unknown:
            record["reason_unknown"] = encoding.solver.reason_unknown()
        else:
            record["proof_status"] = "NO_EXTERNAL_CERTIFICATE_NOT_A_THEOREM"
        runs.append(record)
        if discovered is not None:
            break

    report: dict[str, Any] = {
        "schema": "ai-math-lab.p0054.size54-neighborhood.v1",
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "run_mode": "BOUNDED_DISCOVERY",
        "epistemic_label": "COMPUTED",
        "search_class": "eight-core common-block layered template class",
        "global_lower_bound_claimed": False,
        "reference_path": str(reference_path),
        "reference_sha256": sha256_file(reference_path),
        "reference_candidate_sha256": _semantic_hash(_candidate_semantic(reference)),
        "runs": runs,
        "candidate_found": discovered is not None,
    }
    if discovered is not None:
        report["mathematical_consequence"] = "EXPLICIT_WITNESS_PROVES_sat7_LE_54"
    else:
        report["mathematical_consequence"] = "NONE_RESTRICTED_OR_INCOMPLETE_SEARCH_ONLY"
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


def parse_signed_model(path: Path) -> list[int]:
    """Parse a DIMACS competition-style model file."""

    return [
        int(token)
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines()
        if line.startswith("v ")
        for token in line[2:].split()
        if token != "0"
    ]


def run_solver_configuration(
    configuration: SolverConfiguration,
    solver_path: Path,
    solver_kind: str,
    cnf_path: Path,
    output_directory: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    """Run one bounded SAT configuration without producing a proof trace."""

    model_path = output_directory / f"portfolio-{configuration.name}.model"
    log_path = output_directory / f"portfolio-{configuration.name}.log"
    if solver_kind == "cadical":
        command = [
            str(solver_path),
            *configuration.options,
            "-t",
            str(timeout_seconds),
            "-w",
            str(model_path),
            str(cnf_path),
        ]
    elif solver_kind == "kissat":
        command = [
            str(solver_path),
            *configuration.options,
            f"--time={timeout_seconds}",
            str(cnf_path),
        ]
    else:
        raise ValueError(f"unsupported solver kind: {solver_kind}")
    started = time.perf_counter()
    completed = subprocess.run(command, check=False, capture_output=True, text=True)
    runtime = time.perf_counter() - started
    log_path.write_text(completed.stdout + completed.stderr, encoding="utf-8")
    output = completed.stdout + completed.stderr
    if completed.returncode == 10 and "s SATISFIABLE" in output:
        result = "SAT"
    elif completed.returncode == 20 and "s UNSATISFIABLE" in output:
        result = "UNSAT"
    else:
        result = "UNKNOWN_OR_TIMEOUT"
    if solver_kind == "kissat" and result == "SAT":
        model_lines = [line for line in completed.stdout.splitlines() if line.startswith("v ")]
        model_path.write_text("\n".join(model_lines) + "\n", encoding="utf-8")
    return {
        "configuration": configuration.name,
        "options": list(configuration.options),
        "command": command,
        "returncode": completed.returncode,
        "runtime_seconds": runtime,
        "solver_result": result,
        "epistemic_label": "COMPUTED",
        "model_path": (
            str(model_path) if result == "SAT" and model_path.is_file() else None
        ),
        "log_path": str(log_path),
        "log_sha256": sha256_file(log_path),
        "proof_status": "NO_PROOF_REQUESTED_DISCOVERY_ONLY",
    }


def run_portfolio_search(
    reference_path: Path,
    output_directory: Path,
    solver_path: Path,
    solver_kind: str,
    timeout_seconds: int,
    workers: int,
    oriented: bool,
) -> dict[str, Any]:
    """Run the complete target-54 CNF through a bounded SAT portfolio."""

    if timeout_seconds <= 0:
        raise ValueError("timeout_seconds must be positive")
    if workers <= 0:
        raise ValueError("workers must be positive")
    reference = load_reference_candidate(reference_path)
    output_directory.mkdir(parents=True, exist_ok=True)
    cnf_stem = "core-8-target-54-oriented-small-le-27" if oriented else "core-8-target-54-complete"
    cnf_path = output_directory / f"{cnf_stem}.cnf"
    encoding: CnfEncoding = (
        build_oriented_cnf_encoding(core_size=8, target_size=54, small_bound=27)
        if oriented
        else build_cnf_encoding(core_size=8, target_size=54)
    )
    encoding.cnf.to_file(cnf_path)

    configurations = PORTFOLIO if solver_kind == "cadical" else KISSAT_PORTFOLIO
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        futures = [
            executor.submit(
                run_solver_configuration,
                configuration,
                solver_path,
                solver_kind,
                cnf_path,
                output_directory,
                timeout_seconds,
            )
            for configuration in configurations
        ]
        runs = [future.result() for future in futures]

    candidates: list[dict[str, Any]] = []
    for run in runs:
        if run["solver_result"] != "SAT" or run["model_path"] is None:
            continue
        signed_model = parse_signed_model(Path(run["model_path"]))
        candidate = _candidate_from_signed_model(encoding, 8, signed_model)
        verification = validate_candidate(candidate)
        candidates.append(
            {
                "configuration": run["configuration"],
                "candidate": _candidate_semantic(candidate),
                "verification": verification,
            }
        )

    version = subprocess.run(
        [str(solver_path), "--version"],
        check=False,
        capture_output=True,
        text=True,
    ).stdout.strip()
    report = {
        "schema": "ai-math-lab.p0054.size54-portfolio.v1",
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "run_mode": "BOUNDED_DISCOVERY",
        "epistemic_label": "COMPUTED",
        "search_class": "complete eight-core common-block layered template class",
        "encoding": (
            "oriented_partial-signature_exact_with_small_count_duality_breaker"
            if oriented
            else "three-signature-baseline"
        ),
        "target_size": 54,
        "global_lower_bound_claimed": False,
        "solver": f"{solver_kind} {version}",
        "solver_kind": solver_kind,
        "solver_path": str(solver_path),
        "solver_sha256": sha256_file(solver_path),
        "timeout_seconds_per_configuration": timeout_seconds,
        "cnf_path": str(cnf_path),
        "cnf_sha256": sha256_file(cnf_path),
        "primary_variable_count": encoding.primary_variable_count,
        "auxiliary_variable_count": encoding.auxiliary_variable_count,
        "clause_count": len(encoding.cnf.clauses),
        "reference_candidate_sha256": _semantic_hash(_candidate_semantic(reference)),
        "runs": runs,
        "candidate_found": bool(candidates),
        "candidates": candidates,
        "mathematical_consequence": (
            "EXPLICIT_WITNESS_PROVES_sat7_LE_54"
            if candidates
            else "NONE_INCOMPLETE_DISCOVERY_SEARCH_ONLY"
        ),
    }
    report_path = output_directory / "portfolio-report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    neighborhood = subparsers.add_parser("neighborhood")
    neighborhood.add_argument("--reference", type=Path, default=REFERENCE_PATH)
    neighborhood.add_argument(
        "--minimum-overlaps", nargs="+", type=int, default=[54, 53, 52, 51, 50]
    )
    neighborhood.add_argument("--timeout-seconds", type=float, default=60.0)
    neighborhood.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT_DIRECTORY / "neighborhood-report.json",
    )

    portfolio = subparsers.add_parser("portfolio")
    portfolio.add_argument("--reference", type=Path, default=REFERENCE_PATH)
    portfolio.add_argument("--solver", type=Path, required=True)
    portfolio.add_argument("--solver-kind", choices=("cadical", "kissat"), default="cadical")
    portfolio.add_argument("--timeout-seconds", type=int, default=600)
    portfolio.add_argument("--workers", type=int, default=4)
    portfolio.add_argument(
        "--oriented",
        action="store_true",
        help="use the exact one-clause saturation reduction and safe small<=27 duality breaker",
    )
    portfolio.add_argument("--output-directory", type=Path, default=DEFAULT_OUTPUT_DIRECTORY)
    return parser.parse_args()


def main() -> None:
    """Run the requested bounded discovery mode."""

    args = parse_args()
    if args.command == "neighborhood":
        report = run_neighborhood_search(
            args.reference,
            args.output,
            tuple(args.minimum_overlaps),
            args.timeout_seconds,
        )
    elif args.command == "portfolio":
        report = run_portfolio_search(
            args.reference,
            args.output_directory,
            args.solver,
            args.solver_kind,
            args.timeout_seconds,
            args.workers,
            args.oriented,
        )
    else:
        raise AssertionError("unreachable")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
