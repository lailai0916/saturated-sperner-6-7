#!/usr/bin/env python3
"""Generate split Lean certificates for four-row support-cover completeness."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "AiMathLab/P0054G419"
CHUNK_COUNT = 256


def theorem_name(index: int) -> str:
    return f"four_minimal_support_cover_chunk_{index:03d}"


def module_name(index: int) -> str:
    return f"KernelACoverCompleteCheck{index:03d}"


def generate_check(index: int) -> str:
    return f"""import AiMathLab.P0054G419.KernelACoverComplete

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed chunk checks 64 support masks by kernel reduction.
theorem {theorem_name(index)} :
    fourMinimalSupportCoverChunkCheck {index} = true := by
  rfl

end AiMathLab.P0054.G419
"""


def generate_aggregate() -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054G419.{module_name(index)}"
        for index in range(CHUNK_COUNT)
    )
    theorems = ",\n    ".join(
        theorem_name(index) for index in range(CHUNK_COUNT)
    )
    return f"""{imports}

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
theorem four_minimal_support_cover_chunks :
    (List.range 256).all fourMinimalSupportCoverChunkCheck = true := by
  simp only [List.range_zero, List.range_succ, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, {theorems}]

theorem four_minimal_support_cover_mask_check (mask : Fin 16384) :
    fourMinimalSupportCoverMaskCheck mask.val = true := by
  have hChunkLt : mask.val / 64 < 256 := by omega
  have hChunk := List.all_eq_true.mp four_minimal_support_cover_chunks
    (mask.val / 64) (List.mem_range.mpr hChunkLt)
  have hOffsetLt : mask.val % 64 < 64 := Nat.mod_lt _ (by omega)
  have hMask := List.all_eq_true.mp hChunk
    (mask.val / 64 * 64 + mask.val % 64)
    (List.mem_map.mpr ⟨mask.val % 64, List.mem_range.mpr hOffsetLt, rfl⟩)
  simpa [fourMinimalSupportCoverChunkCheck, Nat.div_add_mod'] using hMask

theorem four_minimal_support_index_covers_complete
    (C : Finset FourSupportIndex) (hC : fourMinimalSupportCover C) :
    ∃ L ∈ fourMinimalSupportIndexCovers, L.toFinset = C := by
  let mask : Fin 16384 := ⟨fourSupportIndexMask C, fourSupportIndexMask_lt C⟩
  have hCheck := four_minimal_support_cover_mask_check mask
  have hDecode := fourSupportIndexFinsetForMask_indexMask C
  simp only [fourMinimalSupportCoverMaskCheck, mask, hDecode, hC,
    decide_true, Bool.not_true, Bool.false_or] at hCheck
  obtain ⟨L, hL, hLC⟩ := List.any_eq_true.mp hCheck
  exact ⟨L, hL, of_decide_eq_true hLC⟩

end AiMathLab.P0054.G419
"""


def write_if_changed(path: Path, content: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return
    path.write_text(content, encoding="utf-8")


def main() -> None:
    expected = set()
    for index in range(CHUNK_COUNT):
        path = OUTPUT / f"{module_name(index)}.lean"
        expected.add(path)
        write_if_changed(path, generate_check(index))
    for path in OUTPUT.glob("KernelACoverCompleteCheck[0-9][0-9][0-9].lean"):
        if path not in expected:
            path.unlink()
    write_if_changed(OUTPUT / "KernelACoverCompleteChecks.lean", generate_aggregate())
    print(f"generated {CHUNK_COUNT} support-cover completeness checks")


if __name__ == "__main__":
    main()
