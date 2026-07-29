#!/usr/bin/env python3
"""Generate split Lean certificates for the G4.19 Kernel A search."""

from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERIFY = (
    ROOT
    / "Problems/P0054/experiments/g4.12-exact-fifty-four/verify-middle-six-ten.py"
)
OUTPUT = ROOT / "AiMathLab/P0054G419"
GROUP_BUDGET = 50
HEAVY_THRESHOLD = 50
MASK_BLOCK_SIZE = 64
MASK_BLOCK_COUNT = (1 << 14) // MASK_BLOCK_SIZE


def load_verifier():
    spec = importlib.util.spec_from_file_location("p0054_middle_six_ten", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lean_list(values: tuple[int, ...] | list[int]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def feasible_masks_and_vectors(verifier):
    all_covers = verifier.minimal_support_covers()
    results = []
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
        current = verifier.multiplicity_vectors_for_active(active, covers)
        vectors.extend(current)
        results.append((mask, active, covers, search_nodes(verifier, active, covers)))
    return results, vectors


def search_nodes(verifier, active, covers) -> int:
    values = [0] * 14
    degrees = [0] * 4
    nodes = 0

    def visit(position: int) -> None:
        nonlocal nodes
        nodes += 1
        if position == len(active):
            return
        index = active[position]
        support = verifier.SUPPORTS[index]
        capacity = min(
            6 - degrees[row] for row in range(4) if support & (1 << row)
        )
        for value in range(1, capacity + 1):
            values[index] = value
            for row in range(4):
                if support & (1 << row):
                    degrees[row] += value
            if verifier.weighted_profile(covers, tuple(values))[0] <= 6:
                visit(position + 1)
            for row in range(4):
                if support & (1 << row):
                    degrees[row] -= value
        values[index] = 0

    visit(0)
    return nodes


def partition_groups(results):
    groups = []
    current = []
    current_cost = 0
    for mask, _, _, cost in results:
        if cost > HEAVY_THRESHOLD:
            continue
        if current and current_cost + cost > GROUP_BUDGET:
            groups.append(tuple(current))
            current = []
            current_cost = 0
        current.append(mask)
        current_cost += cost
        if current_cost >= GROUP_BUDGET:
            groups.append(tuple(current))
            current = []
            current_cost = 0
    if current:
        groups.append(tuple(current))
    return tuple(groups)


def generate_data(vectors) -> str:
    rows = ",\n".join(f"    {lean_list(vector)}" for vector in vectors)
    return f"""import Mathlib

namespace AiMathLab.P0054.G419

def fourMultiplicityCertificate : List (List Nat) :=
  [
{rows}
  ]

end AiMathLab.P0054.G419
"""


def theorem_name(index: int) -> str:
    return f"four_kernel_a_classification_group_{index:03d}"


def module_name(index: int) -> str:
    return f"KernelAClassificationCheck{index:03d}"


def heavy_theorem_name(mask: int) -> str:
    return f"four_kernel_a_classification_mask_{mask:05d}"


def heavy_module_name(mask: int) -> str:
    return f"KernelAClassificationMask{mask:05d}"


def block_theorem_name(index: int) -> str:
    return f"four_kernel_a_classification_block_{index:03d}"


def block_module_name(index: int) -> str:
    return f"KernelAClassificationBlock{index:03d}"


def prefix_theorem_name(mask: int, prefix: tuple[int, int]) -> str:
    return f"four_kernel_a_classification_prefix_{mask:05d}_{prefix[0]}_{prefix[1]}"


def prefix_module_name(mask: int, prefix: tuple[int, int]) -> str:
    return f"KernelAClassificationPrefix{mask:05d}{prefix[0]}{prefix[1]}"


def generate_group(index: int, masks: tuple[int, ...]) -> str:
    return f"""import AiMathLab.P0054G419.KernelAFinite

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group is split so kernel reduction remains incremental.
theorem {theorem_name(index)} :
    {lean_list(masks)}.all fourKernelAClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G419
"""


def admissible_prefixes(verifier, active, covers) -> tuple[tuple[int, int], ...]:
    values = [0] * 14
    degrees = [0] * 4
    result = []
    first_index, second_index = active[:2]
    first_support = verifier.SUPPORTS[first_index]
    second_support = verifier.SUPPORTS[second_index]
    first_capacity = min(
        6 - degrees[row] for row in range(4) if first_support & (1 << row)
    )
    for first in range(1, first_capacity + 1):
        values[first_index] = first
        for row in range(4):
            if first_support & (1 << row):
                degrees[row] += first
        if verifier.weighted_profile(covers, tuple(values))[0] <= 6:
            second_capacity = min(
                6 - degrees[row]
                for row in range(4)
                if second_support & (1 << row)
            )
            for second in range(1, second_capacity + 1):
                values[second_index] = second
                for row in range(4):
                    if second_support & (1 << row):
                        degrees[row] += second
                if verifier.weighted_profile(covers, tuple(values))[0] <= 6:
                    result.append((first, second))
                for row in range(4):
                    if second_support & (1 << row):
                        degrees[row] -= second
            values[second_index] = 0
        for row in range(4):
            if first_support & (1 << row):
                degrees[row] -= first
        values[first_index] = 0
    return tuple(result)


def generate_prefix(mask: int, prefix: tuple[int, int]) -> str:
    return f"""import AiMathLab.P0054G419.KernelAFinite

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed prefix leaves a kernel-reducible residual multiplicity tree.
theorem {prefix_theorem_name(mask, prefix)} :
    fourKernelAClassificationValuesCheck {mask} {lean_list(prefix)} = true := by
  rfl

end AiMathLab.P0054.G419
"""


def generate_heavy(mask: int, active: tuple[int, ...], prefixes) -> str:
    first, second, *remaining = active
    imports = "\n".join(
        f"import AiMathLab.P0054G419.{prefix_module_name(mask, prefix)}"
        for prefix in prefixes
    )
    prefix_set = set(prefixes)
    cases = []
    for left in range(1, 7):
        for right in range(1, 7):
            prefix = (left, right)
            if prefix in prefix_set:
                cases.append(f"  · exact {prefix_theorem_name(mask, prefix)}")
            else:
                cases.extend(
                    [
                        "  · have hFalse :",
                        (
                            "      fourKernelATwoPrefixAdmissible "
                            f"{mask} {left} {right} = false := by rfl"
                        ),
                        "    rw [hFalse] at hAdmissible",
                        "    contradiction",
                    ]
                )
    return f"""{imports}

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into kernel-reducible branches.
theorem {heavy_theorem_name(mask)} :
    fourKernelAClassificationMaskCheck {mask} = true := by
  apply fourKernelAClassificationMaskCheck_of_two_prefixes
    {mask} {first} {second} {lean_list(remaining)} rfl rfl
  intro k hk l hl
  have hAdmissible : fourKernelATwoPrefixAdmissible {mask} k l = true := by
    simp only [fourKernelATwoPrefixAdmissible]
    rw [show fourMaskSupports {mask} = {lean_list(active)} by rfl]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hk, decide_eq_true hl⟩
  have hkBounds : 1 ≤ k ∧ k ≤ 6 := by
    have hkRange := (List.mem_filter.mp hk).1
    simp only [List.mem_map, List.mem_range] at hkRange
    obtain ⟨n, hn, rfl⟩ := hkRange
    omega
  have hlBounds : 1 ≤ l ∧ l ≤ 6 := by
    have hlRange := (List.mem_filter.mp hl).1
    simp only [List.mem_map, List.mem_range] at hlRange
    obtain ⟨n, hn, rfl⟩ := hlRange
    omega
  have hkLower := hkBounds.1
  have hkUpper := hkBounds.2
  have hlLower := hlBounds.1
  have hlUpper := hlBounds.2
  interval_cases k <;> interval_cases l
{chr(10).join(cases)}

end AiMathLab.P0054.G419
"""


def mask_proof(mask: int, group_of_mask: dict[int, int], heavy_masks: set[int]) -> str:
    if mask in heavy_masks:
        return f"  · exact {heavy_theorem_name(mask)}"
    if mask not in group_of_mask:
        return "  · rfl"
    index = group_of_mask[mask]
    return "\n".join(
        [
            "  · exact fourKernelAClassificationMaskCheck_of_list",
            f"      {theorem_name(index)} (by decide)",
        ]
    )


def generate_block(
    index: int,
    group_of_mask: dict[int, int],
    heavy_masks: set[int],
) -> str:
    start = index * MASK_BLOCK_SIZE
    masks = range(start, start + MASK_BLOCK_SIZE)
    group_imports = sorted({group_of_mask[mask] for mask in masks if mask in group_of_mask})
    heavy_imports = sorted(mask for mask in masks if mask in heavy_masks)
    imports = [
        "import AiMathLab.P0054G419.KernelAFinite",
        *(f"import AiMathLab.P0054G419.{module_name(group)}" for group in group_imports),
        *(f"import AiMathLab.P0054G419.{heavy_module_name(mask)}" for mask in heavy_imports),
    ]
    cases = "\n".join(mask_proof(mask, group_of_mask, heavy_masks) for mask in masks)
    return f"""{chr(10).join(imports)}

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem {block_theorem_name(index)} (offset : Fin {MASK_BLOCK_SIZE}) :
    fourKernelAClassificationMaskCheck ({start} + offset.val) = true := by
  fin_cases offset
{cases}

end AiMathLab.P0054.G419
"""


def generate_aggregate() -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054G419.{block_module_name(index)}"
        for index in range(MASK_BLOCK_COUNT)
    )
    cases = []
    for index in range(MASK_BLOCK_COUNT):
        cases.append(f"  · exact {block_theorem_name(index)} offset")
    return f"""{imports}

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Exhaustive block dispatch connects every split certificate to the full range.
theorem four_kernel_a_classification_block_check
    (block : Fin {MASK_BLOCK_COUNT}) (offset : Fin {MASK_BLOCK_SIZE}) :
    fourKernelAClassificationMaskCheck
      (block.val * {MASK_BLOCK_SIZE} + offset.val) = true := by
  fin_cases block
{chr(10).join(cases)}

theorem four_kernel_a_classification_mask_check (mask : Fin 16384) :
    fourKernelAClassificationMaskCheck mask.val = true := by
  let block : Fin {MASK_BLOCK_COUNT} :=
    ⟨mask.val / {MASK_BLOCK_SIZE}, by omega⟩
  let offset : Fin {MASK_BLOCK_SIZE} :=
    ⟨mask.val % {MASK_BLOCK_SIZE}, Nat.mod_lt _ (by omega)⟩
  have hCheck := four_kernel_a_classification_block_check block offset
  simpa [block, offset, Nat.div_add_mod'] using hCheck

theorem four_kernel_a_classification_check :
    (List.range 16384).all fourKernelAClassificationMaskCheck = true := by
  rw [List.all_eq_true]
  intro mask hMask
  exact four_kernel_a_classification_mask_check
    ⟨mask, List.mem_range.mp hMask⟩

end AiMathLab.P0054.G419
"""


def write_dispatch(
    group_of_mask: dict[int, int],
    heavy_masks: set[int],
    aggregate_filename: str = "KernelAClassificationChecks.lean",
) -> None:
    for index in range(MASK_BLOCK_COUNT):
        (OUTPUT / f"{block_module_name(index)}.lean").write_text(
            generate_block(index, group_of_mask, heavy_masks), encoding="utf-8"
        )
    (OUTPUT / aggregate_filename).write_text(generate_aggregate(), encoding="utf-8")


def main() -> None:
    verifier = load_verifier()
    results, vectors = feasible_masks_and_vectors(verifier)
    if len(results) != 1064 or len(vectors) != 95:
        raise AssertionError((len(results), len(vectors)))
    groups = partition_groups(results)
    heavy = tuple(result for result in results if result[3] > HEAVY_THRESHOLD)
    prefixes_by_mask = {
        mask: admissible_prefixes(verifier, active, covers)
        for mask, active, covers, _ in heavy
    }
    for path in OUTPUT.glob("KernelAClassificationCheck[0-9][0-9][0-9].lean"):
        path.unlink()
    for path in OUTPUT.glob("KernelAClassificationMask[0-9][0-9][0-9][0-9][0-9].lean"):
        path.unlink()
    for path in OUTPUT.glob("KernelAClassificationPrefix[0-9]*.lean"):
        path.unlink()
    for path in OUTPUT.glob("KernelAClassificationBlock[0-9][0-9][0-9].lean"):
        path.unlink()
    (OUTPUT / "KernelAData.lean").write_text(generate_data(vectors), encoding="utf-8")
    for index, masks in enumerate(groups):
        (OUTPUT / f"{module_name(index)}.lean").write_text(
            generate_group(index, masks), encoding="utf-8"
        )
    for mask, active, _, _ in heavy:
        for prefix in prefixes_by_mask[mask]:
            (OUTPUT / f"{prefix_module_name(mask, prefix)}.lean").write_text(
                generate_prefix(mask, prefix), encoding="utf-8"
            )
        (OUTPUT / f"{heavy_module_name(mask)}.lean").write_text(
            generate_heavy(mask, active, prefixes_by_mask[mask]), encoding="utf-8"
        )
    group_of_mask = {
        mask: index for index, group in enumerate(groups) for mask in group
    }
    heavy_masks = {mask for mask, _, _, _ in heavy}
    write_dispatch(group_of_mask, heavy_masks)
    print(
        f"generated {len(groups)} groups, {len(heavy)} split masks, "
        f"and {MASK_BLOCK_COUNT} dispatch blocks "
        f"with {sum(map(len, prefixes_by_mask.values()))} prefixes "
        f"for {len(results)} masks and {len(vectors)} vectors"
    )


if __name__ == "__main__":
    main()
