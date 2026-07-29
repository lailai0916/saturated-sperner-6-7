#!/usr/bin/env python3
"""Generate split Lean certificates for the G4.20 middle four-row search."""

from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERIFY = (
    ROOT
    / "Problems/P0054/experiments/g4.12-exact-fifty-four/"
    "middle-four-row-kernels.py"
)
OUTPUT = ROOT / "AiMathLab/P0054G420"
GROUP_BUDGET = 100
HEAVY_THRESHOLD = 100
BLOCK_SIZE = 64
BLOCK_COUNT = (1 << 14) // BLOCK_SIZE
SPLIT_PREFIX_MASKS = {203, 207, 219, 222, 235, 237, 243}
PREFIX_LEAF_BUDGET = 15
PREFIX_LEAF_BUDGET_OVERRIDES = {219: 1, 235: 1}


def load_verifier():
    spec = importlib.util.spec_from_file_location("p0054_middle_four", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lean_list(values) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def search_nodes(verifier, active, covers) -> tuple[int, int]:
    active_set = set(active)
    values = [1 if index in active_set else 0 for index in range(14)]
    degrees = [0] * 4
    nodes = 0
    leaves = 0

    def visit(position: int) -> None:
        nonlocal nodes, leaves
        nodes += 1
        if position == len(active):
            if min(degrees) >= 3:
                leaves += 1
            return
        index = active[position]
        support = verifier.SUPPORTS[index]
        capacity = min(
            8 - degrees[row] for row in range(4) if support & (1 << row)
        )
        for value in range(1, capacity + 1):
            values[index] = value
            for row in range(4):
                if support & (1 << row):
                    degrees[row] += value
            total, pairs = verifier.weighted_counts(covers, tuple(values))
            if total <= 8 and pairs <= 4:
                visit(position + 1)
            for row in range(4):
                if support & (1 << row):
                    degrees[row] -= value
        values[index] = 1

    visit(0)
    return nodes, leaves


def feasible_masks(verifier):
    results = []
    vector_count = 0
    for mask in range(1, 1 << 14):
        active = tuple(index for index in range(14) if mask & (1 << index))
        support_degrees = tuple(
            sum(bool(verifier.SUPPORTS[index] & (1 << row)) for index in active)
            for row in range(4)
        )
        if min(support_degrees) == 0 or max(support_degrees) > 8:
            continue
        if not verifier.is_clutter(active):
            continue
        active_set = frozenset(active)
        covers = tuple(
            cover for cover in verifier.COVERS if frozenset(cover) <= active_set
        )
        if not covers or len(covers) > 8:
            continue
        if sum(len(cover) == 2 for cover in covers) > 4:
            continue
        if frozenset().union(*(frozenset(cover) for cover in covers)) != active_set:
            continue
        cost, leaves = search_nodes(verifier, active, covers)
        vector_count += leaves
        results.append((mask, active, covers, cost))
    if len(results) != 1448 or vector_count != 49:
        raise AssertionError((len(results), vector_count))
    return tuple(results)


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


def admissible_prefixes(verifier, active, covers):
    active_set = set(active)
    values = [1 if index in active_set else 0 for index in range(14)]
    degrees = [0] * 4
    result = []
    first_index, second_index = active[:2]
    first_support = verifier.SUPPORTS[first_index]
    second_support = verifier.SUPPORTS[second_index]
    for first in range(1, 9):
        values[first_index] = first
        for row in range(4):
            if first_support & (1 << row):
                degrees[row] += first
        total, pairs = verifier.weighted_counts(covers, tuple(values))
        if total <= 8 and pairs <= 4:
            capacity = min(
                8 - degrees[row]
                for row in range(4)
                if second_support & (1 << row)
            )
            for second in range(1, capacity + 1):
                values[second_index] = second
                for row in range(4):
                    if second_support & (1 << row):
                        degrees[row] += second
                total, pairs = verifier.weighted_counts(covers, tuple(values))
                if total <= 8 and pairs <= 4:
                    result.append((first, second))
                for row in range(4):
                    if second_support & (1 << row):
                        degrees[row] -= second
            values[second_index] = 1
        for row in range(4):
            if first_support & (1 << row):
                degrees[row] -= first
        values[first_index] = 1
    return tuple(result)


def residual_prefix_data(verifier, active, covers, prefix):
    active_set = set(active)
    values = [1 if index in active_set else 0 for index in range(14)]
    degrees = [0] * 4

    for position, value in enumerate(prefix):
        index = active[position]
        support = verifier.SUPPORTS[index]
        values[index] = value
        for row in range(4):
            if support & (1 << row):
                degrees[row] += value

    nodes = 0

    def visit(position: int) -> None:
        nonlocal nodes
        nodes += 1
        if position == len(active):
            return
        index = active[position]
        support = verifier.SUPPORTS[index]
        capacity = min(
            8 - degrees[row] for row in range(4) if support & (1 << row)
        )
        for value in range(1, capacity + 1):
            values[index] = value
            for row in range(4):
                if support & (1 << row):
                    degrees[row] += value
            total, pairs = verifier.weighted_counts(covers, tuple(values))
            if total <= 8 and pairs <= 4:
                visit(position + 1)
            for row in range(4):
                if support & (1 << row):
                    degrees[row] -= value
        values[index] = 1

    position = len(prefix)
    if position == len(active):
        return 1, ()

    index = active[position]
    support = verifier.SUPPORTS[index]
    capacity = min(8 - degrees[row] for row in range(4) if support & (1 << row))
    next_values = []
    for value in range(1, capacity + 1):
        values[index] = value
        for row in range(4):
            if support & (1 << row):
                degrees[row] += value
        total, pairs = verifier.weighted_counts(covers, tuple(values))
        if total <= 8 and pairs <= 4:
            next_values.append(value)
        for row in range(4):
            if support & (1 << row):
                degrees[row] -= value
    values[index] = 1

    visit(position)
    return nodes, tuple(next_values)


def split_prefix_tree(verifier, mask, active, covers, roots):
    tree = {}
    leaf_budget = PREFIX_LEAF_BUDGET_OVERRIDES.get(mask, PREFIX_LEAF_BUDGET)

    def visit(prefix):
        cost, next_values = residual_prefix_data(verifier, active, covers, prefix)
        if cost <= leaf_budget or not next_values:
            tree[prefix] = ()
            return
        children = tuple((*prefix, value) for value in next_values)
        tree[prefix] = children
        for child in children:
            visit(child)

    for root in roots:
        visit(root)
    return tree


def group_theorem_name(index: int) -> str:
    return f"middle_four_classification_group_{index:03d}"


def group_module_name(index: int) -> str:
    return f"MiddleFourClassificationCheck{index:03d}"


def mask_theorem_name(mask: int) -> str:
    return f"middle_four_classification_mask_{mask:05d}"


def mask_module_name(mask: int) -> str:
    return f"MiddleFourClassificationMask{mask:05d}"


def prefixes_theorem_name(mask: int) -> str:
    return f"middle_four_classification_prefixes_{mask:05d}"


def prefixes_module_name(mask: int) -> str:
    return f"MiddleFourClassificationPrefixes{mask:05d}"


def split_prefix_theorem_name(mask: int, prefix) -> str:
    suffix = "_".join(map(str, prefix))
    return f"middle_four_classification_prefix_{mask:05d}_{suffix}"


def split_prefix_module_name(mask: int, prefix) -> str:
    suffix = "".join(map(str, prefix))
    return f"MiddleFourClassificationPrefix{mask:05d}{suffix}"


def block_theorem_name(index: int) -> str:
    return f"middle_four_classification_block_{index:03d}"


def block_module_name(index: int) -> str:
    return f"MiddleFourClassificationBlock{index:03d}"


def generate_group(index: int, masks) -> str:
    return f"""import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem {group_theorem_name(index)} :
    {lean_list(masks)}.all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
"""


def generate_prefixes(mask: int, prefixes) -> str:
    values_list = lean_list(lean_list(prefix) for prefix in prefixes)
    return f"""import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed prefix leaves a kernel-reducible residual multiplicity tree.
theorem {prefixes_theorem_name(mask)} :
    {values_list}.all (middleFourClassificationValuesCheck {mask}) = true := by
  rfl

end AiMathLab.P0054.G420
"""


def generate_split_prefix_leaf(mask: int, prefix) -> str:
    return f"""import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed prefix leaves a bounded residual search tree.
theorem {split_prefix_theorem_name(mask, prefix)} :
    middleFourClassificationValuesCheck {mask} {lean_list(prefix)} = true := by
  rfl

end AiMathLab.P0054.G420
"""


def generate_split_prefix_parent(mask: int, active, prefix, children) -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054G420.{split_prefix_module_name(mask, child)}"
        for child in children
    )
    next_values = tuple(child[-1] for child in children)
    alternatives = " ∨ ".join(f"k = {value}" for value in next_values)
    patterns = " | ".join("rfl" for _ in children)
    fixed_rewrites = ", ".join("if_pos (by decide)" for _ in prefix)
    cases = []
    for child in children:
        child_rewrites = ", ".join("if_pos (by decide)" for _ in child)
        cases.extend(
            [
                f"  · have h := {split_prefix_theorem_name(mask, child)}",
                "    unfold middleFourClassificationValuesCheck at h",
                "    rw [hSupports] at h",
                "    simp only [middleFourClassificationValuesCheckAux] at h",
                f"    rw [{child_rewrites}] at h",
                "    exact h",
            ]
        )
    return f"""{imports}

namespace AiMathLab.P0054.G420

open G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem {split_prefix_theorem_name(mask, prefix)} :
    middleFourClassificationValuesCheck {mask} {lean_list(prefix)} = true := by
  have hSupports : fourMaskSupports {mask} = {lean_list(active)} := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [{fixed_rewrites}]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : {alternatives} := by
    change k ∈ {lean_list(next_values)} at hk
    simpa using hk
  rcases hkValues with {patterns}
{chr(10).join(cases)}

end AiMathLab.P0054.G420
"""


def generate_split_prefixes(mask: int, prefixes) -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054G420.{split_prefix_module_name(mask, prefix)}"
        for prefix in prefixes
    )
    cases = "\n".join(
        f"  · exact {split_prefix_theorem_name(mask, prefix)}"
        for prefix in prefixes
    )
    values_list = lean_list(lean_list(prefix) for prefix in prefixes)
    alternatives = " | ".join("rfl" for _ in prefixes)
    return f"""{imports}

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem {prefixes_theorem_name(mask)} :
    {values_list}.all (middleFourClassificationValuesCheck {mask}) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with {alternatives}
{cases}

end AiMathLab.P0054.G420
"""


def generate_prefix_00243_1_1() -> str:
    return """import AiMathLab.P0054G420.MiddleFourClassificationPrefix00243111
import AiMathLab.P0054G420.MiddleFourClassificationPrefix00243112
import AiMathLab.P0054G420.MiddleFourClassificationPrefix00243113

namespace AiMathLab.P0054.G420

open G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The third multiplicity splits the only oversized two-value branch.
theorem middle_four_classification_prefix_00243_1_1 :
    middleFourClassificationValuesCheck 243 [1, 1] = true := by
  have hSupports : fourMaskSupports 243 = [0, 1, 4, 5, 6, 7] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 ∨ k = 2 ∨ k = 3 := by
    change k ∈ [1, 2, 3] at hk
    simpa using hk
  rcases hkValues with rfl | rfl | rfl
  · have h := middle_four_classification_prefix_00243_1_1_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00243_1_1_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00243_1_1_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.G420
"""


def generate_heavy(mask: int, active, prefixes) -> str:
    first, second, *remaining = active
    imports = f"import AiMathLab.P0054G420.{prefixes_module_name(mask)}"
    prefix_set = set(prefixes)
    cases = []
    for left in range(1, 9):
        for right in range(1, 9):
            prefix = (left, right)
            if prefix in prefix_set:
                cases.extend(
                    [
                        "  · exact middleFourClassificationValuesCheck_of_list",
                        f"      {prefixes_theorem_name(mask)} (by decide)",
                    ]
                )
            else:
                cases.extend(
                    [
                        "  · have hFalse :",
                        (
                            "      middleFourTwoPrefixAdmissible "
                            f"{mask} {left} {right} = false := by rfl"
                        ),
                        "    rw [hFalse] at hAdmissible",
                        "    contradiction",
                    ]
                )
    return f"""{imports}

namespace AiMathLab.P0054.G420

open G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into bounded branches.
theorem {mask_theorem_name(mask)} :
    middleFourClassificationMaskCheck {mask} = true := by
  apply middleFourClassificationMaskCheck_of_two_prefixes
    {mask} {first} {second} {lean_list(remaining)} rfl rfl
  intro k hk l hl
  have hAdmissible : middleFourTwoPrefixAdmissible {mask} k l = true := by
    simp only [middleFourTwoPrefixAdmissible]
    rw [show fourMaskSupports {mask} = {lean_list(active)} by rfl]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hk, decide_eq_true hl⟩
  have hkBounds : 1 ≤ k ∧ k ≤ 8 := by
    have hkRange := (List.mem_filter.mp hk).1
    simp only [List.mem_map, List.mem_range] at hkRange
    obtain ⟨n, hn, rfl⟩ := hkRange
    omega
  have hlBounds : 1 ≤ l ∧ l ≤ 8 := by
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

end AiMathLab.P0054.G420
"""


def mask_proof(mask: int, group_of_mask, heavy_masks) -> str:
    if mask in heavy_masks:
        return f"  · exact {mask_theorem_name(mask)}"
    if mask not in group_of_mask:
        return "  · rfl"
    index = group_of_mask[mask]
    return "\n".join(
        [
            "  · exact middleFourClassificationMaskCheck_of_list",
            f"      {group_theorem_name(index)} (by decide)",
        ]
    )


def generate_block(index: int, group_of_mask, heavy_masks) -> str:
    start = index * BLOCK_SIZE
    masks = range(start, start + BLOCK_SIZE)
    group_imports = sorted(
        {group_of_mask[mask] for mask in masks if mask in group_of_mask}
    )
    heavy_imports = sorted(mask for mask in masks if mask in heavy_masks)
    imports = [
        "import AiMathLab.P0054G420.MiddleFourFinite",
        *(
            f"import AiMathLab.P0054G420.{group_module_name(group)}"
            for group in group_imports
        ),
        *(
            f"import AiMathLab.P0054G420.{mask_module_name(mask)}"
            for mask in heavy_imports
        ),
    ]
    cases = "\n".join(mask_proof(mask, group_of_mask, heavy_masks) for mask in masks)
    return f"""{chr(10).join(imports)}

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem {block_theorem_name(index)} (offset : Fin {BLOCK_SIZE}) :
    middleFourClassificationMaskCheck ({start} + offset.val) = true := by
  fin_cases offset
{cases}

end AiMathLab.P0054.G420
"""


def generate_aggregate() -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054G420.{block_module_name(index)}"
        for index in range(BLOCK_COUNT)
    )
    cases = "\n".join(
        f"  · exact {block_theorem_name(index)} offset"
        for index in range(BLOCK_COUNT)
    )
    return f"""{imports}

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Exhaustive block dispatch covers all fourteen-bit support masks.
theorem middle_four_classification_block_check
    (block : Fin {BLOCK_COUNT}) (offset : Fin {BLOCK_SIZE}) :
    middleFourClassificationMaskCheck
      (block.val * {BLOCK_SIZE} + offset.val) = true := by
  fin_cases block
{cases}

theorem middle_four_classification_mask_check (mask : Fin 16384) :
    middleFourClassificationMaskCheck mask.val = true := by
  let block : Fin {BLOCK_COUNT} :=
    ⟨mask.val / {BLOCK_SIZE}, by omega⟩
  let offset : Fin {BLOCK_SIZE} :=
    ⟨mask.val % {BLOCK_SIZE}, Nat.mod_lt _ (by omega)⟩
  have hCheck := middle_four_classification_block_check block offset
  simpa [block, offset, Nat.div_add_mod'] using hCheck

theorem middle_four_classification_check :
    (List.range 16384).all middleFourClassificationMaskCheck = true := by
  rw [List.all_eq_true]
  intro mask hMask
  exact middle_four_classification_mask_check
    ⟨mask, List.mem_range.mp hMask⟩

end AiMathLab.P0054.G420
"""


def write_if_changed(path: Path, content: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return
    path.write_text(content, encoding="utf-8")


def main() -> None:
    verifier = load_verifier()
    results = feasible_masks(verifier)
    groups = partition_groups(results)
    heavy = tuple(result for result in results if result[3] > HEAVY_THRESHOLD)
    prefixes_by_mask = {
        mask: admissible_prefixes(verifier, active, covers)
        for mask, active, covers, _ in heavy
    }
    for index, masks in enumerate(groups):
        write_if_changed(
            OUTPUT / f"{group_module_name(index)}.lean",
            generate_group(index, masks),
        )
    for mask, active, covers, _cost in heavy:
        if mask in SPLIT_PREFIX_MASKS:
            tree = split_prefix_tree(
                verifier, mask, active, covers, prefixes_by_mask[mask]
            )
            for prefix, children in tree.items():
                if children:
                    content = generate_split_prefix_parent(
                        mask, active, prefix, children
                    )
                else:
                    content = generate_split_prefix_leaf(mask, prefix)
                write_if_changed(
                    OUTPUT / f"{split_prefix_module_name(mask, prefix)}.lean",
                    content,
                )
            write_if_changed(
                OUTPUT / f"{prefixes_module_name(mask)}.lean",
                generate_split_prefixes(mask, prefixes_by_mask[mask]),
            )
        else:
            write_if_changed(
                OUTPUT / f"{prefixes_module_name(mask)}.lean",
                generate_prefixes(mask, prefixes_by_mask[mask]),
            )
        write_if_changed(
            OUTPUT / f"{mask_module_name(mask)}.lean",
            generate_heavy(mask, active, prefixes_by_mask[mask]),
        )
    group_of_mask = {
        mask: index for index, group in enumerate(groups) for mask in group
    }
    heavy_masks = {mask for mask, _, _, _ in heavy}
    for index in range(BLOCK_COUNT):
        write_if_changed(
            OUTPUT / f"{block_module_name(index)}.lean",
            generate_block(index, group_of_mask, heavy_masks),
        )
    write_if_changed(
        OUTPUT / "MiddleFourClassificationChecks.lean", generate_aggregate()
    )
    print(
        f"generated {len(groups)} groups, {len(heavy)} split masks, "
        f"{len(heavy)} prefix certificates over "
        f"{sum(map(len, prefixes_by_mask.values()))} branches, "
        f"and {BLOCK_COUNT} dispatch blocks"
    )


if __name__ == "__main__":
    main()
