#!/usr/bin/env python3
"""Generate the exact four-row certificate for the P0054 (7,9) split."""

from __future__ import annotations

import importlib.util
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE_GENERATOR = ROOT / "scripts/p0054_generate_g420_middle_four_lean.py"
VERIFY = (
    ROOT
    / "Problems/P0054/experiments/g4.12-exact-fifty-four/"
    "middle-four-row-kernels.py"
)
BASE_FINITE = ROOT / "AiMathLab/P0054G420/MiddleFourFinite.lean"
FINITE = ROOT / "AiMathLab/P0054MiddleSevenNineFourFinite.lean"
OUTPUT = ROOT / "AiMathLab/P0054MiddleSevenNineFour"

MAXIMUM = 9
GROUP_BUDGET = 200
HEAVY_THRESHOLD = 200
BLOCK_SIZE = 64
BLOCK_COUNT = (1 << 14) // BLOCK_SIZE
PREFIX_LEAF_BUDGET = 30
PREFIX_LEAF_BUDGET_OVERRIDES = {219: 1, 235: 1}


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def search_vectors(verifier, active, covers):
    active_set = set(active)
    values = [1 if index in active_set else 0 for index in range(14)]
    degrees = [0] * 4
    nodes = 0
    vectors: list[tuple[int, ...]] = []

    def visit(position: int) -> None:
        nonlocal nodes
        nodes += 1
        if position == len(active):
            if min(degrees) >= 3:
                vectors.append(tuple(values))
            return
        index = active[position]
        support = verifier.SUPPORTS[index]
        capacity = min(
            MAXIMUM - degrees[row]
            for row in range(4)
            if support & (1 << row)
        )
        for value in range(1, capacity + 1):
            values[index] = value
            for row in range(4):
                if support & (1 << row):
                    degrees[row] += value
            total, pairs = verifier.weighted_counts(covers, tuple(values))
            if total <= MAXIMUM and pairs <= 4:
                visit(position + 1)
            for row in range(4):
                if support & (1 << row):
                    degrees[row] -= value
        values[index] = 1

    visit(0)
    return nodes, tuple(vectors)


def feasible_masks(verifier):
    results = []
    vectors: list[tuple[int, ...]] = []
    for mask in range(1, 1 << 14):
        active = tuple(index for index in range(14) if mask & (1 << index))
        support_degrees = tuple(
            sum(bool(verifier.SUPPORTS[index] & (1 << row)) for index in active)
            for row in range(4)
        )
        if min(support_degrees) == 0 or max(support_degrees) > MAXIMUM:
            continue
        if not verifier.is_clutter(active):
            continue
        active_set = frozenset(active)
        covers = tuple(
            cover for cover in verifier.COVERS if frozenset(cover) <= active_set
        )
        if not covers or len(covers) > MAXIMUM:
            continue
        if sum(len(cover) == 2 for cover in covers) > 4:
            continue
        if frozenset().union(*(frozenset(cover) for cover in covers)) != active_set:
            continue
        cost, current = search_vectors(verifier, active, covers)
        results.append((mask, active, covers, cost))
        vectors.extend(current)
    if len(results) != 1592 or len(vectors) != 136:
        raise AssertionError((len(results), len(vectors)))
    return tuple(results), tuple(vectors)


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
    for first in range(1, MAXIMUM + 1):
        values[first_index] = first
        for row in range(4):
            if first_support & (1 << row):
                degrees[row] += first
        total, pairs = verifier.weighted_counts(covers, tuple(values))
        if total <= MAXIMUM and pairs <= 4:
            capacity = min(
                MAXIMUM - degrees[row]
                for row in range(4)
                if second_support & (1 << row)
            )
            for second in range(1, capacity + 1):
                values[second_index] = second
                for row in range(4):
                    if second_support & (1 << row):
                        degrees[row] += second
                total, pairs = verifier.weighted_counts(covers, tuple(values))
                if total <= MAXIMUM and pairs <= 4:
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
            MAXIMUM - degrees[row]
            for row in range(4)
            if support & (1 << row)
        )
        for value in range(1, capacity + 1):
            values[index] = value
            for row in range(4):
                if support & (1 << row):
                    degrees[row] += value
            total, pairs = verifier.weighted_counts(covers, tuple(values))
            if total <= MAXIMUM and pairs <= 4:
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
    capacity = min(
        MAXIMUM - degrees[row]
        for row in range(4)
        if support & (1 << row)
    )
    next_values = []
    for value in range(1, capacity + 1):
        values[index] = value
        for row in range(4):
            if support & (1 << row):
                degrees[row] += value
        total, pairs = verifier.weighted_counts(covers, tuple(values))
        if total <= MAXIMUM and pairs <= 4:
            next_values.append(value)
        for row in range(4):
            if support & (1 << row):
                degrees[row] -= value
    values[index] = 1
    visit(position)
    return nodes, tuple(next_values)


def split_prefix_tree(verifier, mask, active, covers, roots, leaf_budget):
    tree = {}

    def visit(prefix):
        cost, next_values = residual_prefix_data(
            verifier, active, covers, prefix
        )
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


def transform_source(source: str, *, numeric_bounds: bool = False) -> str:
    source = source.replace(
        "import AiMathLab.P0054G420.MiddleFourFinite",
        "import AiMathLab.P0054MiddleSevenNineFourFinite",
    )
    source = source.replace(
        "AiMathLab.P0054G420.",
        "AiMathLab.P0054MiddleSevenNineFour.",
    )
    source = source.replace(
        "namespace AiMathLab.P0054.G420",
        "namespace AiMathLab.P0054.MiddleSevenNineFinite",
    )
    source = source.replace(
        "end AiMathLab.P0054.G420",
        "end AiMathLab.P0054.MiddleSevenNineFinite",
    )
    source = source.replace("open G413 G419\n", "open G413 G419 G420\n")
    source = source.replace("open G419\n", "open G419 G420\n")
    if numeric_bounds:
        source = re.sub(r"\b8\b", "9", source)
    return source


def lean_list(values) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def generate_finite(vectors) -> str:
    source = BASE_FINITE.read_text(encoding="utf-8")
    source = transform_source(source, numeric_bounds=True)
    source = source.replace(
        "import AiMathLab.P0054MiddleSevenNineFour.FourKernelPair",
        "import AiMathLab.P0054G420.FourKernelPair",
    )
    certificate = "def middleFourMultiplicityCertificate : List (List Nat) :=\n  [\n"
    certificate += ",\n".join(f"    {lean_list(vector)}" for vector in vectors)
    certificate += "\n  ]\n\n"
    certificate_pattern = (
        r"def middleFourMultiplicityCertificate : List \(List Nat\) :=\n"
        r".*?\n\ndef middleFourMultiplicityInCertificate"
    )
    source = re.sub(
        certificate_pattern,
        certificate + "def middleFourMultiplicityInCertificate",
        source,
        flags=re.DOTALL,
    )
    source = source.replace(
        "# Common four-row finite certificate",
        "# Exact four-row finite certificate for the seven-plus-nine split",
    )
    return source


def generate_heavy(base, mask: int, active, prefixes) -> str:
    """Generate all 9 x 9 prefix cases (the G420 source has only 8 x 8)."""
    first, second, *remaining = active
    imports = (
        "import AiMathLab.P0054MiddleSevenNineFour."
        f"{base.prefixes_module_name(mask)}"
    )
    prefix_set = set(prefixes)
    cases = []
    for left in range(1, MAXIMUM + 1):
        for right in range(1, MAXIMUM + 1):
            prefix = (left, right)
            if prefix in prefix_set:
                cases.extend(
                    [
                        "  · exact middleFourClassificationValuesCheck_of_list",
                        f"      {base.prefixes_theorem_name(mask)} (by decide)",
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

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into bounded branches.
theorem {base.mask_theorem_name(mask)} :
    middleFourClassificationMaskCheck {mask} = true := by
  apply middleFourClassificationMaskCheck_of_two_prefixes
    {mask} {first} {second} {lean_list(remaining)} rfl rfl
  intro k hk l hl
  have hAdmissible : middleFourTwoPrefixAdmissible {mask} k l = true := by
    simp only [middleFourTwoPrefixAdmissible]
    rw [show fourMaskSupports {mask} = {lean_list(active)} by rfl]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hk, decide_eq_true hl⟩
  have hkBounds : 1 ≤ k ∧ k ≤ {MAXIMUM} := by
    have hkRange := (List.mem_filter.mp hk).1
    simp only [List.mem_map, List.mem_range] at hkRange
    obtain ⟨n, hn, rfl⟩ := hkRange
    omega
  have hlBounds : 1 ≤ l ∧ l ≤ {MAXIMUM} := by
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

end AiMathLab.P0054.MiddleSevenNineFinite
"""


def write_if_changed(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return
    path.write_text(content, encoding="utf-8")


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def chain_modules(
    paths, lanes: int = 1, segments: int = 1
) -> tuple[str, ...]:
    """Add dependency lanes that bound simultaneous module elaboration."""
    if lanes < 1:
        raise ValueError("a build chain needs at least one lane")
    if segments < 1:
        raise ValueError("a build chain needs at least one segment")
    paths = tuple(sorted(paths))
    by_module = {module_name(path): path for path in paths}
    imports = {}
    for path in paths:
        source = path.read_text(encoding="utf-8")
        imports[path] = tuple(
            by_module[name]
            for name in re.findall(r"^import (\S+)$", source, flags=re.MULTILINE)
            if name in by_module
        )

    ordered = []
    permanent = set()
    temporary = set()

    def visit(path: Path) -> None:
        if path in permanent:
            return
        if path in temporary:
            raise AssertionError(f"import cycle at {path}")
        temporary.add(path)
        for dependency in imports[path]:
            visit(dependency)
        temporary.remove(path)
        permanent.add(path)
        ordered.append(path)

    for path in paths:
        visit(path)

    if not ordered:
        raise AssertionError("a build chain needs a root")
    if segments > len(ordered):
        raise ValueError("a build chain cannot have more segments than modules")

    roots = []
    for segment in range(segments):
        start = len(ordered) * segment // segments
        stop = len(ordered) * (segment + 1) // segments
        for index in range(start + lanes, stop):
            path = ordered[index]
            dependency = module_name(ordered[index - lanes])
            source = path.read_text(encoding="utf-8")
            line = f"import {dependency}\n"
            if line not in source:
                write_if_changed(path, line + source)
        roots.extend(module_name(path) for path in ordered[max(start, stop - lanes) : stop])
    return tuple(roots)


def chain_residual_classification_sinks(lanes: int = 2) -> tuple[str, ...]:
    """Bound Lake parallelism for generated classification roots left orphaned.

    Incremental generation intentionally preserves sources from earlier thresholds.
    Some of those generated modules are no longer imported by the current certificate
    graph, but Lake's library glob still builds every one of them.  Link precisely the
    currently unimported generated leaves into a small number of dependency lanes so a
    full-library build cannot elaborate hundreds of old roots simultaneously.
    """
    imported_modules = set()
    for path in (ROOT / "AiMathLab").rglob("*.lean"):
        source = path.read_text(encoding="utf-8")
        imported_modules.update(
            re.findall(r"^(?:public )?import (\S+)$", source, flags=re.MULTILINE)
        )

    generated_leaf = re.compile(
        r"MiddleFourClassification(?:Prefix|Mask|Check)\d+\.lean"
    )
    sinks = tuple(
        path
        for path in OUTPUT.glob("*.lean")
        if generated_leaf.fullmatch(path.name)
        and module_name(path) not in imported_modules
    )
    if not sinks:
        return ()
    return chain_modules(sinks, lanes=lanes)


def main() -> None:
    base = load_module("p0054_g420_generator", BASE_GENERATOR)
    verifier = load_module("p0054_middle_four", VERIFY)
    results, vectors = feasible_masks(verifier)
    write_if_changed(FINITE, generate_finite(vectors))

    groups = partition_groups(results)
    heavy = tuple(result for result in results if result[3] > HEAVY_THRESHOLD)
    prefixes_by_mask = {
        mask: admissible_prefixes(verifier, active, covers)
        for mask, active, covers, _ in heavy
    }
    group_paths = []
    for index, masks in enumerate(groups):
        path = OUTPUT / f"{base.group_module_name(index)}.lean"
        write_if_changed(
            path,
            transform_source(base.generate_group(index, masks)),
        )
        group_paths.append(path)
    prefix_paths = []
    mask_paths = []
    for mask, active, covers, _cost in heavy:
        leaf_budget = PREFIX_LEAF_BUDGET_OVERRIDES.get(
            mask, PREFIX_LEAF_BUDGET
        )
        tree = split_prefix_tree(
            verifier,
            mask,
            active,
            covers,
            prefixes_by_mask[mask],
            leaf_budget,
        )
        for prefix, children in tree.items():
            if children:
                content = base.generate_split_prefix_parent(
                    mask, active, prefix, children
                )
            else:
                content = base.generate_split_prefix_leaf(mask, prefix)
            path = OUTPUT / f"{base.split_prefix_module_name(mask, prefix)}.lean"
            write_if_changed(path, transform_source(content))
            prefix_paths.append(path)
        path = OUTPUT / f"{base.prefixes_module_name(mask)}.lean"
        write_if_changed(
            path,
            transform_source(
                base.generate_split_prefixes(mask, prefixes_by_mask[mask])
            ),
        )
        prefix_paths.append(path)
        path = OUTPUT / f"{base.mask_module_name(mask)}.lean"
        write_if_changed(
            path,
            generate_heavy(base, mask, active, prefixes_by_mask[mask]),
        )
        mask_paths.append(path)
    group_of_mask = {
        mask: index for index, group in enumerate(groups) for mask in group
    }
    heavy_masks = {mask for mask, _, _, _ in heavy}
    block_paths = []
    for index in range(BLOCK_COUNT):
        path = OUTPUT / f"{base.block_module_name(index)}.lean"
        write_if_changed(
            path,
            transform_source(
                base.generate_block(index, group_of_mask, heavy_masks)
            ),
        )
        block_paths.append(path)
    write_if_changed(
        OUTPUT / "MiddleFourClassificationChecks.lean",
        transform_source(base.generate_aggregate()),
    )
    prefix_roots = chain_modules(prefix_paths)
    mask_roots = chain_modules(mask_paths)
    group_roots = chain_modules(group_paths)
    block_roots = chain_modules(block_paths)
    residual_roots = chain_residual_classification_sinks()
    print(
        f"generated {len(vectors)} vectors, {len(groups)} groups, "
        f"{len(heavy)} heavy masks, {sum(map(len, prefixes_by_mask.values()))} "
        f"root prefixes, and {BLOCK_COUNT} blocks\n"
        f"prefix roots: {' '.join(prefix_roots)}\n"
        f"mask roots: {' '.join(mask_roots)}\n"
        f"group roots: {' '.join(group_roots)}\n"
        f"block roots: {' '.join(block_roots)}\n"
        f"residual roots: {' '.join(residual_roots)}"
    )


if __name__ == "__main__":
    main()
