from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

import pytest

from scripts.p0054_size54_discovery import sha256_file

ROOT = Path(__file__).parents[1]
LAYER_MANIFEST = (
    ROOT
    / "Problems/P0054/experiments/size54-g3-layer-bounds/verification-manifest.json"
)
FIXED_MANIFEST = (
    ROOT
    / "Problems/P0054/experiments/size54-g3-system/fixed-middle14/verification-manifest.json"
)
COMPLETE_MANIFEST = (
    ROOT
    / "Problems/P0054/experiments/size54-g3-system/complete/verification-manifest.json"
)
PROFILE_MANIFEST = (
    ROOT
    / "Problems/P0054/experiments/size54-g3-profiles/profile-search-manifest.json"
)


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _repo_path(text: str) -> Path:
    return ROOT / text


def _require_archived_artifact(path: Path) -> None:
    if path.is_file():
        return
    message = f"archived release artifact is not present: {path}"
    if os.environ.get("P0054_REQUIRE_ARCHIVE_ARTIFACTS") == "1":
        pytest.fail(message)
    pytest.skip(message)


def test_layer_bound_certificates_and_hashes() -> None:
    report = _load(LAYER_MANIFEST)
    assert report["epistemic_label"] == "PROVED"
    semantic = report["semantic"]
    assert semantic["all_certificates_verified"]
    assert semantic["proved_layer_minima_if_verified"] == [1, 6, 12, 14, 12, 6, 1]
    assert semantic["proved_total_independent_layer_lower_bound_if_verified"] == 52
    for record in semantic["records"]:
        assert record["solver_result"] == "UNSAT"
        assert record["checker_result"] == "VERIFIED"
        for path_key, hash_key in (
            ("cnf_path", "cnf_sha256"),
            ("proof_path", "proof_sha256"),
            ("solver_log", "solver_log_sha256"),
            ("checker_log", "checker_log_sha256"),
        ):
            path = _repo_path(record[path_key])
            _require_archived_artifact(path)
            assert sha256_file(path) == record[hash_key]


def test_fixed_middle_nonextension_certificate_and_hashes() -> None:
    report = _load(FIXED_MANIFEST)
    semantic = report["semantic"]
    assert semantic["fixed_middle14"]
    assert semantic["solver_result"] == "UNSAT_VERIFIED"
    evidence = semantic["result_evidence"]
    for path_key, hash_key in (
        ("cnf_path", "cnf_sha256"),
        ("solver_log", "solver_log_sha256"),
    ):
        path = _repo_path(semantic[path_key])
        _require_archived_artifact(path)
        assert sha256_file(path) == semantic[hash_key]
    for path_key, hash_key in (
        ("proof_path", "proof_sha256"),
        ("checker_log", "checker_log_sha256"),
    ):
        path = _repo_path(evidence[path_key])
        _require_archived_artifact(path)
        assert sha256_file(path) == evidence[hash_key]


def test_complete_timeout_has_no_claim_or_incomplete_trace() -> None:
    report = _load(COMPLETE_MANIFEST)
    semantic = report["semantic"]
    assert report["epistemic_label"] == "COMPUTED"
    assert semantic["solver_result"] == "UNKNOWN_OR_TIMEOUT"
    assert semantic["result_evidence"]["mathematical_consequence"] == "NONE"
    assert not _repo_path(semantic["solver_command"][-1]).exists()


def test_all_profile_runs_are_recorded_without_promotion() -> None:
    report = _load(PROFILE_MANIFEST)
    semantic = report["semantic"]
    assert report["epistemic_label"] == "COMPUTED"
    assert semantic["profile_count"] == 28
    assert semantic["counts"] == {
        "SAT_VERIFIED_CANDIDATE": 0,
        "UNSAT_NO_CERTIFICATE": 0,
        "UNKNOWN_OR_TIMEOUT": 28,
    }
    assert len(semantic["records"]) == 28
    for record in semantic["records"]:
        assert record["solver_result"] == "UNKNOWN_OR_TIMEOUT"
        for path_key, hash_key in (
            ("cnf_path", "cnf_sha256"),
            ("log_path", "log_sha256"),
        ):
            path = _repo_path(record[path_key])
            _require_archived_artifact(path)
            assert sha256_file(path) == record[hash_key]
