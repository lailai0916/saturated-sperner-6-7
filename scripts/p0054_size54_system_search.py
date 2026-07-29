"""Run the proved rank-window reduction on the complete P0054 size-54 target.

The search is complete only for the eight-core common-block layered template
class.  Its additional per-layer upper bounds use the independently checked
single-layer minima ``(1, 6, 12, 14, 12, 6, 1)``: a total-size-at-most-54
candidate has at most two members beyond each corresponding minimum.

A SAT result is accepted only after the four semantic candidate verifiers.  An
UNSAT result is promoted only after DRAT-trim checks the emitted proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from scripts.p0054_layered_sat7 import Template, _candidate_semantic, _semantic_hash
from scripts.p0054_size54_discovery import (
    REFERENCE_PATH,
    parse_signed_model,
    sha256_file,
    validate_candidate,
)
from scripts.p0054_size54_structural import (
    MIDDLE14_TEMPLATES,
    build_rank_window_system_encoding,
    checker_commit,
    decode_rank_window_model,
)

DEFAULT_OUTPUT_DIRECTORY = Path("Problems/P0054/experiments/size54-g3-system")
CERTIFIED_LAYER_MINIMA = (1, 6, 12, 14, 12, 6, 1)
SAFE_LAYER_UPPER_BOUNDS = tuple(value + 2 for value in CERTIFIED_LAYER_MINIMA)


def run_complete_search(
    output_directory: Path,
    solver: Path,
    checker: Path,
    timeout_seconds: int,
    fixed_middle14: bool,
) -> dict[str, Any]:
    """Generate the reduced CNF, solve it, and validate a conclusive result."""

    if timeout_seconds <= 0:
        raise ValueError("timeout_seconds must be positive")
    if not solver.is_file():
        raise FileNotFoundError(solver)
    if not checker.is_file():
        raise FileNotFoundError(checker)
    output_directory.mkdir(parents=True, exist_ok=True)
    fixed_layers: dict[int, tuple[Template, ...]] | None = (
        {3: MIDDLE14_TEMPLATES} if fixed_middle14 else None
    )
    encoding = build_rank_window_system_encoding(
        core_size=8,
        target_size=54,
        layer_upper_bounds=SAFE_LAYER_UPPER_BOUNDS,
        small_bound=27,
        fixed_layers=fixed_layers,
    )
    stem = "core8-target54-rank-window"
    if fixed_middle14:
        stem += "-fixed-middle14"
    cnf_path = output_directory / f"{stem}.cnf"
    proof_path = output_directory / f"{stem}.drat"
    solver_log = output_directory / f"{stem}.kissat.log"
    model_path = output_directory / f"{stem}.model"
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

    if completed.returncode == 10 and "s SATISFIABLE" in combined:
        model_lines = [line for line in completed.stdout.splitlines() if line.startswith("v ")]
        model_path.write_text("\n".join(model_lines) + "\n", encoding="utf-8")
        candidate = decode_rank_window_model(
            encoding, 8, parse_signed_model(model_path)
        )
        verification = validate_candidate(candidate)
        result = "SAT_VERIFIED_CANDIDATE"
        epistemic_label = "PROVED_EXPLICIT_CONSTRUCTION"
        result_evidence: dict[str, Any] = {
            "candidate": _candidate_semantic(candidate),
            "candidate_sha256": _semantic_hash(_candidate_semantic(candidate)),
            "model_path": str(model_path),
            "model_sha256": sha256_file(model_path),
            "verification": verification,
            "mathematical_consequence": "sat(7)<=54",
        }
    elif completed.returncode == 20 and "s UNSATISFIABLE" in combined:
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
            raise RuntimeError("DRAT-trim rejected the complete system proof")
        result = "UNSAT_VERIFIED"
        epistemic_label = "PROVED_CLASS_RESTRICTED_LOWER_BOUND"
        result_evidence = {
            "proof_path": str(proof_path),
            "proof_bytes": proof_path.stat().st_size,
            "proof_sha256": sha256_file(proof_path),
            "checker_log": str(checker_log),
            "checker_log_sha256": sha256_file(checker_log),
            "mathematical_consequence": (
                "no size-at-most-54 system in the eight-core template class"
                if not fixed_middle14
                else "no system extending this fixed middle-layer witness"
            ),
        }
    else:
        result = "UNKNOWN_OR_TIMEOUT"
        epistemic_label = "COMPUTED"
        discarded_incomplete_trace = proof_path.is_file()
        if discarded_incomplete_trace:
            proof_path.unlink()
        result_evidence = {
            "mathematical_consequence": "NONE",
            "discarded_incomplete_proof_trace": discarded_incomplete_trace,
        }

    semantic = {
        "search_class": "eight-core common-block layered template class",
        "fixed_middle14": fixed_middle14,
        "target_size": 54,
        "certified_layer_minima": list(CERTIFIED_LAYER_MINIMA),
        "safe_layer_upper_bounds": list(SAFE_LAYER_UPPER_BOUNDS),
        "small_template_bound": 27,
        "reference_path": str(REFERENCE_PATH),
        "reference_sha256": sha256_file(REFERENCE_PATH),
        "solver": str(solver),
        "solver_sha256": sha256_file(solver),
        "checker": str(checker),
        "checker_sha256": sha256_file(checker),
        "checker_commit": checker_commit(checker),
        "solver_command": command,
        "solver_returncode": completed.returncode,
        "runtime_seconds": runtime_seconds,
        "solver_result": result,
        "primary_variable_count": encoding.primary_variable_count,
        "auxiliary_variable_count": encoding.auxiliary_variable_count,
        "clause_count": len(encoding.cnf.clauses),
        "cnf_path": str(cnf_path),
        "cnf_bytes": cnf_path.stat().st_size,
        "cnf_sha256": sha256_file(cnf_path),
        "solver_log": str(solver_log),
        "solver_log_sha256": sha256_file(solver_log),
        "result_evidence": result_evidence,
    }
    canonical = json.dumps(semantic, sort_keys=True, separators=(",", ":"))
    report = {
        "schema": "ai-math-lab.p0054.size54-rank-window-system.v1",
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "run_mode": "STRUCTURAL_REDUCED_COMPLETE_SEARCH",
        "epistemic_label": epistemic_label,
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
    parser.add_argument("--fixed-middle14", action="store_true")
    parser.add_argument("--output-directory", type=Path, default=DEFAULT_OUTPUT_DIRECTORY)
    return parser.parse_args()


def main() -> None:
    """Run and print the complete reduced search report."""

    args = parse_args()
    report = run_complete_search(
        args.output_directory,
        args.solver,
        args.checker,
        args.timeout_seconds,
        args.fixed_middle14,
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
