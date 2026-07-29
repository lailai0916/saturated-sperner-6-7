#!/usr/bin/env python3
"""Generate bounded Lean certificates for the G4.20 five-row exact-pair gap."""

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

FOUR_CERTIFICATE = {
    (0, 0, 0, 1, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0),
    (0, 0, 0, 0, 1, 2, 0, 1, 1, 1, 0, 0, 0, 0),
    (0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0),
    (0, 0, 1, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0),
    (0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0),
    (0, 0, 1, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0),
}

THREE_CERTIFICATE = {
    (1, 0, 0, 1, 0, 1, 0, 1, 0, 2, 0, 0, 0, 0),
    (1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0),
    (1, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0),
    (1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0),
    (1, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0),
    (1, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0),
    (1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0),
    (1, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0),
    (1, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0),
    (1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0),
    (1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0),
    (1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0),
    (1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0),
    (1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0),
    (1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0),
}


def load_verifier():
    spec = importlib.util.spec_from_file_location("p0054_middle_four", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lean_list(values) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def mask_valid(verifier, mask: int, pair_bound: int) -> bool:
    active = tuple(index for index in range(14) if mask & (1 << index))
    support_degrees = tuple(
        sum(bool(verifier.SUPPORTS[index] & (1 << row)) for index in active)
        for row in range(4)
    )
    if mask == 0 or any(degree <= 0 or degree > 5 for degree in support_degrees):
        return False
    if not verifier.is_clutter(active):
        return False
    active_set = frozenset(active)
    covers = tuple(
        cover for cover in verifier.COVERS if frozenset(cover) <= active_set
    )
    if not covers or len(covers) > 5:
        return False
    if sum(len(cover) == 2 for cover in covers) > pair_bound:
        return False
    return frozenset().union(*(frozenset(cover) for cover in covers)) == active_set


def classification_cost(verifier, mask: int, pair_bound: int, kind: str) -> int:
    active = tuple(index for index in range(14) if mask & (1 << index))
    values = [1 if index in active else 0 for index in range(14)]
    degrees = [0] * 4
    certificate = FOUR_CERTIFICATE if kind == "Four" else THREE_CERTIFICATE
    nodes = 0

    def visit(position: int) -> None:
        nonlocal nodes
        nodes += 1
        if position == len(active):
            if kind == "Four":
                leaf = degrees[0] == 2 and all(
                    3 <= degrees[row] <= 5 for row in (1, 2, 3)
                )
            else:
                leaf = (
                    degrees[0] == 1
                    and all(2 <= degrees[row] <= 5 for row in (1, 2, 3))
                    and sum(degrees[row] == 2 for row in (1, 2, 3)) <= 1
                )
            if leaf and tuple(values) not in certificate:
                raise AssertionError((kind, mask, tuple(values), tuple(degrees)))
            return

        index = active[position]
        support = verifier.SUPPORTS[index]
        for value in range(1, 6):
            if any(
                degrees[row] + value > 5
                for row in range(4)
                if support & (1 << row)
            ):
                continue
            values[index] = value
            for row in range(4):
                if support & (1 << row):
                    degrees[row] += value
            weighted, pairs = verifier.weighted_counts(
                verifier.COVERS, tuple(values)
            )
            if weighted <= 5 and pairs <= pair_bound:
                visit(position + 1)
            for row in range(4):
                if support & (1 << row):
                    degrees[row] -= value
        values[index] = 1

    visit(0)
    return nodes


def feasible_masks(verifier, pair_bound: int, kind: str):
    return tuple(
        (mask, classification_cost(verifier, mask, pair_bound, kind))
        for mask in range(1 << 14)
        if mask_valid(verifier, mask, pair_bound)
    )


def partition_groups(results):
    groups = []
    current = []
    current_cost = 0
    for mask, cost in results:
        if current and current_cost + cost > GROUP_BUDGET:
            groups.append(tuple(current))
            current = []
            current_cost = 0
        current.append(mask)
        current_cost += cost
    if current:
        groups.append(tuple(current))
    return tuple(groups)


def group_def(kind: str, index: int) -> str:
    return f"{kind[0].lower() + kind[1:]}PairExactMaskGroup{index:03d}"


def group_theorem(kind: str, index: int) -> str:
    prefix = "four_exceptional" if kind == "Four" else "three_padded"
    return f"{prefix}_pair_exact_mask_group_{index:03d}"


def group_module(kind: str, index: int) -> str:
    return f"FiveRowPairExactFinite{kind}Check{index:03d}"


def generate_masks(four_groups, three_groups) -> str:
    definitions = []
    for kind, groups in (("Four", four_groups), ("Three", three_groups)):
        for index, group in enumerate(groups):
            definitions.append(
                f"def {group_def(kind, index)} : List Nat :=\n  {lean_list(group)}"
            )
    return f"""import AiMathLab.P0054G420.FiveRowPairExactFinite

namespace AiMathLab.P0054.G420

{chr(10).join(definitions)}

end AiMathLab.P0054.G420
"""


def generate_group(kind: str, index: int, pair_bound: int) -> str:
    if kind == "Four":
        leaf = "fourExceptionalMultiplicityLeafValid"
        accept = "fourExceptionalMultiplicityInCertificate"
    else:
        leaf = "threePaddedMultiplicityLeafValid"
        accept = "threePaddedMultiplicityInCertificate"
    return f"""import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The offline node budget is at most {GROUP_BUDGET}; Lean rechecks the whole group.
theorem {group_theorem(kind, index)} :
    {group_def(kind, index)}.all
      (smallFourClassificationMaskCheck {pair_bound}
        {leaf} {accept}) = true := by
  rfl

end AiMathLab.P0054.G420
"""


def block_module(index: int) -> str:
    return f"FiveRowPairExactFiniteBlock{index:03d}"


def block_theorem(kind: str, index: int) -> str:
    prefix = "four_exceptional" if kind == "Four" else "three_padded"
    return f"{prefix}_pair_exact_block_{index:03d}"


def mask_proof(kind: str, mask: int, group_of_mask) -> str:
    if mask not in group_of_mask:
        return "  · rfl"
    index = group_of_mask[mask]
    return "\n".join(
        [
            "  · exact (List.all_eq_true.mp",
            f"      {group_theorem(kind, index)}) {mask} (by decide)",
        ]
    )


def generate_block(index: int, four_group_of_mask, three_group_of_mask) -> str:
    start = index * 64
    masks = range(start, start + 64)
    imports = ["import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks"]
    for kind, mapping in (
        ("Four", four_group_of_mask),
        ("Three", three_group_of_mask),
    ):
        imports.extend(
            f"import AiMathLab.P0054G420.{group_module(kind, group)}"
            for group in sorted({mapping[mask] for mask in masks if mask in mapping})
        )
    four_cases = "\n".join(
        mask_proof("Four", mask, four_group_of_mask) for mask in masks
    )
    three_cases = "\n".join(
        mask_proof("Three", mask, three_group_of_mask) for mask in masks
    )
    return f"""{chr(10).join(imports)}

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the exceptional case.
theorem {block_theorem("Four", index)} (offset : Fin 64) :
    smallFourClassificationMaskCheck 3
      fourExceptionalMultiplicityLeafValid
      fourExceptionalMultiplicityInCertificate ({start} + offset.val) = true := by
  fin_cases offset
{four_cases}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the padded case.
theorem {block_theorem("Three", index)} (offset : Fin 64) :
    smallFourClassificationMaskCheck 0
      threePaddedMultiplicityLeafValid
      threePaddedMultiplicityInCertificate ({start} + offset.val) = true := by
  fin_cases offset
{three_cases}

end AiMathLab.P0054.G420
"""


def generate_aggregate() -> str:
    imports = [
        f"import AiMathLab.P0054G420.{block_module(index)}"
        for index in range(256)
    ]

    def aggregate(kind: str, pair_bound: int) -> str:
        if kind == "Four":
            prefix = "four_exceptional"
            leaf = "fourExceptionalMultiplicityLeafValid"
            accept = "fourExceptionalMultiplicityInCertificate"
        else:
            prefix = "three_padded"
            leaf = "threePaddedMultiplicityLeafValid"
            accept = "threePaddedMultiplicityInCertificate"
        patterns = "\n".join(
            f"  · exact {block_theorem(kind, index)} offset"
            for index in range(256)
        )
        return f"""set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Exhaustive block dispatch covers every fourteen-bit support mask.
theorem {prefix}_pair_exact_block_check
    (block : Fin 256) (offset : Fin 64) :
    smallFourClassificationMaskCheck {pair_bound}
      {leaf} {accept}
      (block.val * 64 + offset.val) = true := by
  fin_cases block
{patterns}

theorem {prefix}_pair_exact_classification_mask_check
    (mask : Fin 16384) :
    smallFourClassificationMaskCheck {pair_bound}
      {leaf} {accept} mask.val = true := by
  let block : Fin 256 :=
    ⟨mask.val / 64, by omega⟩
  let offset : Fin 64 :=
    ⟨mask.val % 64, Nat.mod_lt _ (by omega)⟩
  have hCheck := {prefix}_pair_exact_block_check block offset
  simpa [block, offset, Nat.div_add_mod'] using hCheck

theorem {prefix}_pair_exact_classification_check :
    (List.range 16384).all
      (smallFourClassificationMaskCheck {pair_bound}
        {leaf} {accept}) = true := by
  rw [List.all_eq_true]
  intro mask hMask
  exact {prefix}_pair_exact_classification_mask_check
    ⟨mask, List.mem_range.mp hMask⟩
"""

    return f"""{chr(10).join(imports)}

namespace AiMathLab.P0054.G420

{aggregate("Four", 3)}
{aggregate("Three", 0)}
end AiMathLab.P0054.G420
"""


def write_if_changed(path: Path, content: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return
    path.write_text(content, encoding="utf-8")


def main() -> None:
    verifier = load_verifier()
    four_results = feasible_masks(verifier, 3, "Four")
    three_results = feasible_masks(verifier, 0, "Three")
    if len(four_results) != 455 or len(three_results) != 59:
        raise AssertionError((len(four_results), len(three_results)))
    four_groups = partition_groups(four_results)
    three_groups = partition_groups(three_results)

    write_if_changed(
        OUTPUT / "FiveRowPairExactFiniteMasks.lean",
        generate_masks(four_groups, three_groups),
    )
    for kind, groups, pair_bound in (
        ("Four", four_groups, 3),
        ("Three", three_groups, 0),
    ):
        for index in range(len(groups)):
            write_if_changed(
                OUTPUT / f"{group_module(kind, index)}.lean",
                generate_group(kind, index, pair_bound),
            )
    four_group_of_mask = {
        mask: index for index, group in enumerate(four_groups) for mask in group
    }
    three_group_of_mask = {
        mask: index for index, group in enumerate(three_groups) for mask in group
    }
    for index in range(256):
        write_if_changed(
            OUTPUT / f"{block_module(index)}.lean",
            generate_block(index, four_group_of_mask, three_group_of_mask),
        )
    write_if_changed(
        OUTPUT / "FiveRowPairExactFiniteChecks.lean",
        generate_aggregate(),
    )
    print(
        f"generated {len(four_groups)} four-mask groups and "
        f"{len(three_groups)} three-mask groups and 256 dispatch blocks"
    )


if __name__ == "__main__":
    main()
