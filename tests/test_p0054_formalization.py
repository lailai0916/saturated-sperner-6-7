from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

from scripts.p0054_generate_lean_witnesses import witness_table
from scripts.p0054_verify_candidate import (
    DEFAULT_INPUT,
    candidate_from_record,
    expanded_family,
)

ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "AiMathLab" / "P0054Size55Core.lean"
MAIN = ROOT / "AiMathLab" / "P0054Size55.lean"
BLOCKS = ROOT / "AiMathLab" / "P0054Size55WitnessBlocks"
MANIFEST = ROOT / "Problems" / "P0054" / "formal" / "witness-table-manifest.json"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_lean_family_matches_the_frozen_candidate_exactly() -> None:
    source = CORE.read_text(encoding="utf-8")
    match = re.search(
        r"def size55Masks : Finset Nat :=\s*\[(.*?)\]\.toFinset",
        source,
        re.DOTALL,
    )
    assert match is not None
    lean_masks = [int(token) for token in re.findall(r"\d+", match.group(1))]
    record = json.loads(DEFAULT_INPUT.read_text(encoding="utf-8"))
    frozen_masks = list(expanded_family(candidate_from_record(record)))
    assert set(lean_masks) == set(frozen_masks)
    assert len(lean_masks) == len(set(lean_masks)) == 55


def test_witness_manifest_and_all_generated_hashes_are_exact() -> None:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert manifest["schema"] == "ai-math-lab.p0054.lean-witness-table.v2"
    assert manifest["source_candidate_sha256"] == (
        "55d0a1e19a024efb944fc9a00ea466bdd6d5b11383f1bd86c1f772d8fb92acac"
    )
    assert manifest["ground_size"] == 11
    assert manifest["row_count"] == 2048
    assert manifest["external_witness_count"] == 1993
    assert manifest["member_row_count"] == 55
    assert manifest["witness_length"] == 8
    assert manifest["block_size"] == 64
    assert manifest["core_sha256"] == _sha256(ROOT / manifest["core_path"])
    assert manifest["aggregate_sha256"] == _sha256(ROOT / manifest["aggregate_path"])
    assert manifest["main_sha256"] == _sha256(ROOT / manifest["main_path"])
    assert len(manifest["blocks"]) == 32
    for record in manifest["blocks"]:
        assert record["sha256"] == _sha256(ROOT / record["path"])


def test_witness_table_semantics_reproduce_from_the_candidate() -> None:
    source = json.loads(DEFAULT_INPUT.read_text(encoding="utf-8"))
    family = expanded_family(candidate_from_record(source))
    rows = witness_table(family)
    semantic = json.dumps(rows, separators=(",", ":")).encode()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert hashlib.sha256(semantic).hexdigest() == manifest["table_semantic_sha256"]
    assert sum(bool(row) for row in rows) == 1993
    assert sum(not row for row in rows) == 55


def test_formalization_has_required_theorems_and_no_trust_shortcuts() -> None:
    sources = [CORE.read_text(encoding="utf-8"), MAIN.read_text(encoding="utf-8")]
    sources.extend(path.read_text(encoding="utf-8") for path in sorted(BLOCKS.glob("*.lean")))
    combined = "\n".join(sources)
    required = (
        "size55_card",
        "size55LayerMasks_crosswalk",
        "size55_layerUnion",
        "size55_seven_sperner",
        "size55_saturated",
        "size55_full_certificate",
        "maskChainWitnessChecker_eq_true",
        "maskChainWitness_sound",
    )
    for name in required:
        assert re.search(rf"\b{name}\b", combined)
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide|run_tac)\b")
    assert forbidden.search(combined) is None


def test_thirty_two_blocks_cover_all_eleven_bit_masks() -> None:
    files = sorted(BLOCKS.glob("Block*.lean"))
    assert [path.stem for path in files] == [f"Block{index:02d}" for index in range(32)]
    for index, path in enumerate(files):
        source = path.read_text(encoding="utf-8")
        assert f"maskSubset ({64 * index} + i.val)" in source
        assert f"theorem size55_witness_block_{index:02d}" in source
        assert "∀ i : Fin 64" in source
    main = MAIN.read_text(encoding="utf-8")
    assert "subsetMask_lt_2048" in main
    assert "maskSubset_subsetMask" in main
