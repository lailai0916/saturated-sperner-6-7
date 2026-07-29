"""Independently verify the P0054 CNF/DRAT artifacts with DRAT-trim."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

CERTIFICATE_DIRECTORY = Path("Problems/P0054/experiments/certificates")
DEFAULT_OUTPUT = CERTIFICATE_DIRECTORY / "verification-manifest.json"

ARTIFACTS = (
    (
        4,
        "core-4-target-55-selfcontained.cnf",
        "core-4-target-55-selfcontained-kissat.drat",
    ),
    (
        5,
        "core-5-target-55-selfcontained.cnf",
        "core-5-target-55-selfcontained-kissat.drat",
    ),
    (
        6,
        "core-6-target-55-selfcontained.cnf",
        "core-6-target-55-selfcontained-kissat.drat",
    ),
    (
        7,
        "core-7-target-55-selfcontained.cnf",
        "core-7-target-55-selfcontained-kissat.drat",
    ),
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def checker_commit(checker: Path) -> str | None:
    result = subprocess.run(
        ["git", "-C", str(checker.parent), "rev-parse", "HEAD"],
        check=False,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip() if result.returncode == 0 else None


def verify_one(checker: Path, core_size: int, cnf_path: Path, proof_path: Path) -> dict[str, Any]:
    result = subprocess.run(
        [str(checker), str(cnf_path), str(proof_path)],
        check=False,
        capture_output=True,
        text=True,
    )
    combined = result.stdout + result.stderr
    verified = result.returncode == 0 and "s VERIFIED" in combined
    if not verified:
        raise RuntimeError(
            f"DRAT verification failed for core {core_size}:\n{combined[-4000:]}"
        )
    log_path = proof_path.with_suffix(proof_path.suffix + ".verify.log")
    log_path.write_text(combined, encoding="utf-8")
    return {
        "core_size": core_size,
        "target_size": 55,
        "cnf_path": str(cnf_path),
        "cnf_bytes": cnf_path.stat().st_size,
        "cnf_sha256": sha256_file(cnf_path),
        "proof_path": str(proof_path),
        "proof_bytes": proof_path.stat().st_size,
        "proof_sha256": sha256_file(proof_path),
        "verification_log": str(log_path),
        "verification_log_sha256": sha256_file(log_path),
        "checker_result": "VERIFIED",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    if not args.checker.is_file():
        raise FileNotFoundError(args.checker)

    records = [
        verify_one(
            args.checker,
            core_size,
            CERTIFICATE_DIRECTORY / cnf_name,
            CERTIFICATE_DIRECTORY / proof_name,
        )
        for core_size, cnf_name, proof_name in ARTIFACTS
    ]
    semantic = {
        "checker": str(args.checker),
        "checker_git_commit": checker_commit(args.checker),
        "records": records,
    }
    canonical = json.dumps(semantic, sort_keys=True, separators=(",", ":"))
    report = {
        "schema": "ai-math-lab.p0054.drat-verification.v1",
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "epistemic_label": "COMPUTED",
        "semantic": semantic,
        "semantic_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
