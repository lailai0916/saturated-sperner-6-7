from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

import pytest

from scripts.p0054_verify_drat import DEFAULT_OUTPUT

SIZE55_MANIFEST = Path("Problems/P0054/experiments/core-8-size-55-manifest.json")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _require_archived_artifact(path: Path) -> None:
    if path.is_file():
        return
    message = f"archived release artifact is not present: {path}"
    if os.environ.get("P0054_REQUIRE_ARCHIVE_ARTIFACTS") == "1":
        pytest.fail(message)
    pytest.skip(message)


def test_saved_drat_verification_manifest_is_self_consistent() -> None:
    manifest = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    assert manifest["schema"] == "ai-math-lab.p0054.drat-verification.v1"
    semantic = manifest["semantic"]
    canonical = json.dumps(semantic, sort_keys=True, separators=(",", ":"))
    assert manifest["semantic_sha256"] == hashlib.sha256(canonical.encode()).hexdigest()
    assert semantic["checker_git_commit"] == "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"
    assert [record["core_size"] for record in semantic["records"]] == [4, 5, 6, 7]
    for record in semantic["records"]:
        assert record["target_size"] == 55
        assert record["checker_result"] == "VERIFIED"
        for prefix in ("cnf", "proof"):
            path = Path(record[f"{prefix}_path"])
            _require_archived_artifact(path)
            assert record[f"{prefix}_sha256"] == _sha256(path)
        log_path = Path(record["verification_log"])
        _require_archived_artifact(log_path)
        assert record["verification_log_sha256"] == _sha256(log_path)
        assert "s VERIFIED" in log_path.read_text(encoding="utf-8")


def test_size55_construction_manifest_is_self_consistent() -> None:
    manifest = json.loads(SIZE55_MANIFEST.read_text(encoding="utf-8"))
    assert manifest["schema"] == "ai-math-lab.p0054.size55-artifacts.v1"
    assert manifest["mathematical_consequence"] == (
        "EXPLICIT_WITNESS_PROVES_sat7_LE_55"
    )
    assert manifest["candidate_semantic_sha256"] == (
        "55d0a1e19a024efb944fc9a00ea466bdd6d5b11383f1bd86c1f772d8fb92acac"
    )
    assert manifest["expanded_family_sha256"] == (
        "8277267a7a9cbc6040432a9d6ffc3f16c540a6013b78bedbd85e6b1e27adde0f"
    )
    for artifact in manifest["artifacts"]:
        path = Path(artifact["path"])
        _require_archived_artifact(path)
        assert artifact["bytes"] == path.stat().st_size
        assert artifact["sha256"] == _sha256(path)
