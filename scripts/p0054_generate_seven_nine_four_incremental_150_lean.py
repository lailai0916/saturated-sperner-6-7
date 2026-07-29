#!/usr/bin/env python3
"""Incrementally split the remaining costly P0054 (7,9) four-row masks.

The first controlled pass already built every prefix and mask whose search
cost exceeds 200.  This pass preserves those source chains and their fresh
olean files, adds prefix trees only for costs 151--200, and repartitions the
remaining direct checks with budget 100.
"""

from __future__ import annotations

import os
from pathlib import Path

import p0054_generate_seven_nine_four_lean as generated

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "AiMathLab/P0054MiddleSevenNineFour"
DIRECT_THRESHOLD = int(os.environ.get("P0054_DIRECT_THRESHOLD", "150"))
BUILT_HEAVY_THRESHOLD = int(
    os.environ.get("P0054_BUILT_HEAVY_THRESHOLD", "200")
)
GROUP_BUDGET = int(os.environ.get("P0054_GROUP_BUDGET", "100"))
PREFIX_LEAF_BUDGET = int(
    os.environ.get("P0054_PREFIX_LEAF_BUDGET", "30")
)


def partition_groups(results):
    groups = []
    current = []
    current_cost = 0
    for mask, _, _, cost in results:
        if cost > DIRECT_THRESHOLD:
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


def main() -> None:
    base = generated.load_module(
        "p0054_g420_generator_incremental", generated.BASE_GENERATOR
    )
    verifier = generated.load_module(
        "p0054_middle_four_incremental", generated.VERIFY
    )
    results, _ = generated.feasible_masks(verifier)
    groups = partition_groups(results)
    added_heavy = tuple(
        result
        for result in results
        if DIRECT_THRESHOLD < result[3] <= BUILT_HEAVY_THRESHOLD
    )
    all_heavy_masks = {
        mask for mask, _, _, cost in results if cost > DIRECT_THRESHOLD
    }

    prefix_paths = []
    mask_paths = []
    for mask, active, covers, _ in added_heavy:
        prefixes = generated.admissible_prefixes(verifier, active, covers)
        tree = generated.split_prefix_tree(
            verifier,
            mask,
            active,
            covers,
            prefixes,
            PREFIX_LEAF_BUDGET,
        )
        for prefix, children in tree.items():
            if children:
                content = base.generate_split_prefix_parent(
                    mask, active, prefix, children
                )
            else:
                content = base.generate_split_prefix_leaf(mask, prefix)
            path = OUTPUT / f"{base.split_prefix_module_name(mask, prefix)}.lean"
            generated.write_if_changed(
                path, generated.transform_source(content)
            )
            prefix_paths.append(path)

        path = OUTPUT / f"{base.prefixes_module_name(mask)}.lean"
        generated.write_if_changed(
            path,
            generated.transform_source(
                base.generate_split_prefixes(mask, prefixes)
            ),
        )
        prefix_paths.append(path)

        path = OUTPUT / f"{base.mask_module_name(mask)}.lean"
        generated.write_if_changed(
            path,
            generated.generate_heavy(base, mask, active, prefixes),
        )
        mask_paths.append(path)

    group_paths = []
    for index, masks in enumerate(groups):
        path = OUTPUT / f"{base.group_module_name(index)}.lean"
        generated.write_if_changed(
            path,
            generated.transform_source(base.generate_group(index, masks)),
        )
        group_paths.append(path)

    group_of_mask = {
        mask: index for index, group in enumerate(groups) for mask in group
    }
    block_paths = []
    for index in range(generated.BLOCK_COUNT):
        path = OUTPUT / f"{base.block_module_name(index)}.lean"
        generated.write_if_changed(
            path,
            generated.transform_source(
                base.generate_block(index, group_of_mask, all_heavy_masks)
            ),
        )
        block_paths.append(path)

    generated.write_if_changed(
        OUTPUT / "MiddleFourClassificationChecks.lean",
        generated.transform_source(base.generate_aggregate()),
    )

    # Prefix leaves stay below the measured two-way memory budget.  Two
    # dependency lanes let one Lake process elaborate at most two of them at
    # once, while masks and the later checks retain their single heavy lane.
    prefix_roots = generated.chain_modules(prefix_paths, lanes=2)
    mask_roots = generated.chain_modules(mask_paths, segments=2)
    group_roots = generated.chain_modules(group_paths, segments=2)
    block_roots = generated.chain_modules(block_paths, segments=2)
    residual_roots = generated.chain_residual_classification_sinks()
    print(
        f"incrementally generated {len(added_heavy)} additional heavy masks, "
        f"{len(prefix_paths)} prefix modules, {len(groups)} groups, and "
        f"{generated.BLOCK_COUNT} blocks\n"
        f"prefix roots: {' '.join(prefix_roots)}\n"
        f"mask roots: {' '.join(mask_roots)}\n"
        f"group roots: {' '.join(group_roots)}\n"
        f"block roots: {' '.join(block_roots)}\n"
        f"residual roots: {' '.join(residual_roots)}"
    )


if __name__ == "__main__":
    main()
