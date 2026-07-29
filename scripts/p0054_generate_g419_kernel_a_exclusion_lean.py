#!/usr/bin/env python3
"""Generate per-vector Lean exclusions for the G4.19 Kernel A certificate."""

from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERIFY = (
    ROOT
    / "Problems/P0054/experiments/g4.12-exact-fifty-four/verify-middle-six-ten.py"
)
OUTPUT = ROOT / "AiMathLab/P0054G419"


def load_verifier():
    spec = importlib.util.spec_from_file_location("p0054_middle_six_ten", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lean_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def feasible_vectors(verifier) -> tuple[tuple[int, ...], ...]:
    all_covers = verifier.minimal_support_covers()
    vectors = []
    for mask in range(1, 1 << 14):
        active = tuple(index for index in range(14) if mask & (1 << index))
        support_degrees = tuple(
            sum(bool(verifier.SUPPORTS[index] & (1 << row)) for index in active)
            for row in range(4)
        )
        if (
            min(support_degrees) == 0
            or max(support_degrees) > 6
            or not verifier.is_clutter(active)
        ):
            continue
        active_set = frozenset(active)
        covers = tuple(cover for cover in all_covers if cover <= active_set)
        if (
            not covers
            or len(covers) > 6
            or frozenset().union(*covers) != active_set
        ):
            continue
        vectors.extend(verifier.multiplicity_vectors_for_active(active, covers))
    return tuple(vectors)


def theorem_name(index: int) -> str:
    return f"four_kernel_a_exclusion_group_{index:03d}"


def module_name(index: int) -> str:
    return f"KernelAExclusionCheck{index:03d}"


def generate_check(index: int, vector: tuple[int, ...]) -> str:
    return f"""import AiMathLab.P0054G419.KernelAExclusion

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The concrete vector expands a bounded compatibility search.
theorem {theorem_name(index)} :
    fourKernelAExclusionCheck
      {lean_list(vector)} = true := by
  rfl

end AiMathLab.P0054.G419
"""


def generate_aggregate(count: int) -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054G419.{module_name(index)}"
        for index in range(count)
    )
    theorems = ",\n    ".join(theorem_name(index) for index in range(count))
    return f"""{imports}

namespace AiMathLab.P0054.G419

theorem four_kernel_a_exclusion_check :
    fourMultiplicityCertificate.all fourKernelAExclusionCheck = true := by
  simp only [fourMultiplicityCertificate, List.all_cons, List.all_nil,
    {theorems}]

theorem four_kernel_a_certificate_incompatible
    {{values : List Nat}} (hValues : values ∈ fourMultiplicityCertificate) :
    fourKernelCompatibleExact values.toArray = false := by
  have hCheck := List.all_eq_true.mp four_kernel_a_exclusion_check values hValues
  simpa [fourKernelAExclusionCheck] using hCheck

end AiMathLab.P0054.G419
"""


def write_if_changed(path: Path, content: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return
    path.write_text(content, encoding="utf-8")


def main() -> None:
    vectors = feasible_vectors(load_verifier())
    if len(vectors) != 95:
        raise AssertionError(len(vectors))
    expected = set()
    for index, vector in enumerate(vectors):
        path = OUTPUT / f"{module_name(index)}.lean"
        expected.add(path)
        write_if_changed(path, generate_check(index, vector))
    for path in OUTPUT.glob("KernelAExclusionCheck[0-9][0-9][0-9].lean"):
        if path not in expected:
            path.unlink()
    write_if_changed(
        OUTPUT / "KernelAExclusionChecks.lean", generate_aggregate(len(vectors))
    )
    print(f"generated {len(vectors)} Kernel A exclusion checks")


if __name__ == "__main__":
    main()
