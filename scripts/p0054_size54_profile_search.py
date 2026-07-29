"""Split the P0054 size-54 target into all 28 two-slack layer profiles.

The certified independent layer minima sum to 52.  Every family of total size
at most 54 is therefore covered by at least one componentwise upper-bound
profile obtained by distributing exactly two indistinguishable slack units
among the seven layers.  These bounded runs are discovery evidence only unless
their UNSAT outputs are later accompanied by checked clausal certificates.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import itertools
import json
import subprocess
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from scripts.p0054_layered_sat7 import _candidate_semantic, _semantic_hash
from scripts.p0054_size54_discovery import parse_signed_model, sha256_file, validate_candidate
from scripts.p0054_size54_structural import (
    build_rank_window_system_encoding,
    decode_rank_window_model,
)
from scripts.p0054_size54_system_search import CERTIFIED_LAYER_MINIMA

DEFAULT_OUTPUT_DIRECTORY = Path("Problems/P0054/experiments/size54-g3-profiles")


def two_slack_profiles() -> tuple[tuple[int, ...], ...]:
    """Return all 28 distributions of two units over seven coordinates."""

    profiles: list[tuple[int, ...]] = []
    for left, right in itertools.combinations_with_replacement(range(7), 2):
        extras = [0] * 7
        extras[left] += 1
        extras[right] += 1
        profiles.append(
            tuple(
                minimum + extra
                for minimum, extra in zip(
                    CERTIFIED_LAYER_MINIMA, extras, strict=True
                )
            )
        )
    return tuple(profiles)


def profile_name(profile: tuple[int, ...]) -> str:
    """Return a stable filesystem-safe name for one profile."""

    return "profile-" + "-".join(str(value) for value in profile)


def _run_profile(
    profile: tuple[int, ...],
    output_directory: Path,
    solver: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    """Run one bounded Kissat discovery instance."""

    name = profile_name(profile)
    cnf_path = output_directory / f"{name}.cnf"
    log_path = output_directory / f"{name}.kissat.log"
    model_path = output_directory / f"{name}.model"
    encoding = build_rank_window_system_encoding(
        core_size=8,
        target_size=54,
        layer_upper_bounds=profile,
        small_bound=27,
    )
    encoding.cnf.to_file(cnf_path)
    command = [str(solver), "--sat", f"--time={timeout_seconds}", str(cnf_path)]
    started = time.perf_counter()
    completed = subprocess.run(command, check=False, capture_output=True, text=True)
    runtime_seconds = time.perf_counter() - started
    combined = completed.stdout + completed.stderr
    log_path.write_text(combined, encoding="utf-8")
    if completed.returncode == 10 and "s SATISFIABLE" in combined:
        model_lines = [line for line in completed.stdout.splitlines() if line.startswith("v ")]
        model_path.write_text("\n".join(model_lines) + "\n", encoding="utf-8")
        candidate = decode_rank_window_model(
            encoding, 8, parse_signed_model(model_path)
        )
        verification = validate_candidate(candidate)
        result = "SAT_VERIFIED_CANDIDATE"
        evidence: dict[str, Any] = {
            "candidate": _candidate_semantic(candidate),
            "candidate_sha256": _semantic_hash(_candidate_semantic(candidate)),
            "model_path": str(model_path),
            "model_sha256": sha256_file(model_path),
            "verification": verification,
        }
    elif completed.returncode == 20 and "s UNSATISFIABLE" in combined:
        result = "UNSAT_NO_CERTIFICATE"
        evidence = {"proof_status": "NOT_A_THEOREM_NO_CERTIFICATE"}
    else:
        result = "UNKNOWN_OR_TIMEOUT"
        evidence = {"mathematical_consequence": "NONE"}
    return {
        "profile": list(profile),
        "profile_name": name,
        "runtime_seconds": runtime_seconds,
        "solver_returncode": completed.returncode,
        "solver_result": result,
        "epistemic_label": (
            "PROVED_EXPLICIT_CONSTRUCTION"
            if result == "SAT_VERIFIED_CANDIDATE"
            else "COMPUTED"
        ),
        "primary_variable_count": encoding.primary_variable_count,
        "auxiliary_variable_count": encoding.auxiliary_variable_count,
        "clause_count": len(encoding.cnf.clauses),
        "cnf_path": str(cnf_path),
        "cnf_sha256": sha256_file(cnf_path),
        "log_path": str(log_path),
        "log_sha256": sha256_file(log_path),
        "evidence": evidence,
    }


def run_profile_search(
    output_directory: Path,
    solver: Path,
    timeout_seconds: int,
    workers: int,
) -> dict[str, Any]:
    """Run all profiles and save a complete discovery manifest."""

    if timeout_seconds <= 0:
        raise ValueError("timeout_seconds must be positive")
    if workers <= 0:
        raise ValueError("workers must be positive")
    if not solver.is_file():
        raise FileNotFoundError(solver)
    output_directory.mkdir(parents=True, exist_ok=True)
    profiles = two_slack_profiles()
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        futures = [
            executor.submit(
                _run_profile,
                profile,
                output_directory,
                solver,
                timeout_seconds,
            )
            for profile in profiles
        ]
        records = [future.result() for future in futures]
    candidates = [
        record
        for record in records
        if record["solver_result"] == "SAT_VERIFIED_CANDIDATE"
    ]
    counts = {
        result: sum(record["solver_result"] == result for record in records)
        for result in (
            "SAT_VERIFIED_CANDIDATE",
            "UNSAT_NO_CERTIFICATE",
            "UNKNOWN_OR_TIMEOUT",
        )
    }
    semantic = {
        "certified_layer_minima": list(CERTIFIED_LAYER_MINIMA),
        "profile_count": len(profiles),
        "coverage_argument": (
            "every nonnegative actual slack vector of sum at most two is "
            "componentwise bounded by a listed vector of sum exactly two"
        ),
        "solver": str(solver),
        "solver_sha256": sha256_file(solver),
        "timeout_seconds_per_profile": timeout_seconds,
        "workers": workers,
        "counts": counts,
        "records": records,
        "candidate_found": bool(candidates),
    }
    canonical = json.dumps(semantic, sort_keys=True, separators=(",", ":"))
    report = {
        "schema": "ai-math-lab.p0054.size54-profile-search.v1",
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "run_mode": "BOUNDED_PROFILE_DISCOVERY",
        "epistemic_label": "PROVED" if candidates else "COMPUTED",
        "global_sat7_lower_bound_claimed": False,
        "semantic": semantic,
        "semantic_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
    }
    report_path = output_directory / "profile-search-manifest.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=60)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--output-directory", type=Path, default=DEFAULT_OUTPUT_DIRECTORY)
    return parser.parse_args()


def main() -> None:
    """Run and print the profile discovery report."""

    args = parse_args()
    report = run_profile_search(
        args.output_directory,
        args.solver,
        args.timeout_seconds,
        args.workers,
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
