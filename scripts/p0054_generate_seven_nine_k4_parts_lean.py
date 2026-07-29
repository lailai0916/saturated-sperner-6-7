#!/usr/bin/env python3
"""Generate memory-bounded K4 certificate parts and chunk aggregators."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "AiMathLab"
BASE_CHUNK_COUNTS = (27, 9, 9, 9, 9)
PART_COUNT = 3
CHUNK_WIDTH = 81
BASES = (
    ((3, 4, 5), (2, 3, 6), (1, 4, 6), (1, 2, 5),
     (0, 5, 6), (0, 2, 4), (0, 1, 3)),
    ((3, 4, 5), (2, 3, 6), (1, 4, 6), (1, 2, 5),
     (0, 5, 6), (0, 2, 4), (0, 1, 3, 6)),
    ((3, 4, 5), (2, 3, 6), (1, 4, 6), (1, 2, 5),
     (0, 5, 6), (0, 2, 4, 6), (0, 1, 3)),
    ((3, 4, 5), (2, 3, 6), (1, 4, 6), (1, 2, 5, 6),
     (0, 5, 6), (0, 2, 4), (0, 1, 3)),
    ((3, 4, 5, 6), (2, 3, 6), (1, 4, 6), (1, 2, 5),
     (0, 5, 6), (0, 2, 4), (0, 1, 3)),
)


@dataclass(frozen=True)
class Part:
    base: int
    chunk: int
    part: int

    @property
    def module(self) -> str:
        return (
            "AiMathLab.P0054MiddleSevenNineK4Part"
            f"{self.base}_{self.chunk:02d}_{self.part}"
        )

    @property
    def path(self) -> Path:
        return LEAN / f"P0054MiddleSevenNineK4Part{self.base}_{self.chunk:02d}_{self.part}.lean"


def write_if_changed(path: Path, content: str) -> None:
    if not path.exists() or path.read_text(encoding="utf-8") != content:
        path.write_text(content, encoding="utf-8")


def powerset(values: tuple[int, ...]) -> list[tuple[int, ...]]:
    if not values:
        return [()]
    tail = powerset(values[1:])
    return tail + [(values[0], *row) for row in tail]


def row_mask(row: tuple[int, ...]) -> int:
    return sum(1 << point for point in row)


def old_pair_codes(
    base: tuple[tuple[int, ...], ...],
) -> list[tuple[int, int]]:
    subsets = powerset(tuple(range(7)))
    base_degree = [sum(point in row for row in base) for point in range(7)]
    result: list[tuple[int, int]] = []
    for first in subsets:
        for second in subsets:
            if all(
                base_degree[point]
                + int(point in first)
                + int(point in second)
                <= 4
                for point in range(7)
            ):
                result.append((row_mask(first), row_mask(second)))
    return result


def lean_pairs(values: list[tuple[int, int]]) -> str:
    lines: list[str] = []
    for start in range(0, len(values), 9):
        group = values[start : start + 9]
        suffix = "," if start + 9 < len(values) else ""
        lines.append("      " + ", ".join(f"({a}, {b})" for a, b in group) + suffix)
    return "\n".join(lines)


def render_data(all_pairs: list[list[tuple[int, int]]]) -> str:
    base_blocks: list[str] = []
    for pairs in all_pairs:
        chunks = [
            pairs[start : start + CHUNK_WIDTH]
            for start in range(0, len(pairs), CHUNK_WIDTH)
        ]
        chunk_blocks = [f"    [\n{lean_pairs(chunk)}\n    ]" for chunk in chunks]
        base_blocks.append("  [\n" + ",\n".join(chunk_blocks) + "\n  ]")
    data = ",\n".join(base_blocks)
    return f"""import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

/-!
# Generated old-pair data for the seven-plus-nine K4 certificate

The generator records only row bit masks.  The finite core independently
checks that flattening these chunks gives exactly the definition-level list
of all admissible old-row pairs for each of the five bases.
-/

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

abbrev SevenNineK4DataPoint := Fin 28

def sevenNineK4DecodeOldRow (mask : Nat) :
    Finset SevenNineK4DataPoint :=
  Finset.univ.filter fun point => Nat.testBit mask point.val = true

def sevenNineK4OldPairCodeChunks :
    List (List (List (Nat × Nat))) :=
[
{data}
]

def sevenNineK4OldPairDataChunk (baseIndex chunkIndex : Nat) :
    List (Finset SevenNineK4DataPoint × Finset SevenNineK4DataPoint) :=
  ((sevenNineK4OldPairCodeChunks.getD baseIndex []).getD chunkIndex []).map
    fun pair =>
      (sevenNineK4DecodeOldRow pair.1, sevenNineK4DecodeOldRow pair.2)

end AiMathLab.P0054.MiddleSevenNineK4Finite
"""


def render_part(spec: Part, previous: Part | None) -> str:
    imported = (
        previous.module
        if previous is not None
        else "AiMathLab.P0054MiddleSevenNineK4FiniteCore"
    )
    return f"""import {imported}

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks 27 old-row pairs from one K4 certificate chunk.
theorem sevenNineK4_part_{spec.base}_{spec.chunk:02d}_{spec.part}_check :
    sevenNineK4ChunkPartCheck {spec.base} {spec.chunk} {spec.part} = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineK4Finite
"""


def render_chunk(base: int, chunk: int, previous: tuple[int, int] | None) -> str:
    imports: list[str] = []
    if previous is not None:
        imports.append(
            "AiMathLab.P0054MiddleSevenNineK4Chunk"
            f"{previous[0]}_{previous[1]:02d}"
        )
    else:
        imports.append("AiMathLab.P0054MiddleSevenNineK4FiniteCore")
    imports.extend(
        f"AiMathLab.P0054MiddleSevenNineK4Part{base}_{chunk:02d}_{part}"
        for part in range(PART_COUNT)
    )
    import_block = "\n".join(f"import {module}" for module in imports)
    return f"""{import_block}

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_{base}_{chunk:02d}_check :
    sevenNineK4ChunkCheck {base} {chunk} = true :=
  sevenNineK4ChunkCheck_of_parts {base} {chunk}
    (by decide)
    sevenNineK4_part_{base}_{chunk:02d}_0_check
    sevenNineK4_part_{base}_{chunk:02d}_1_check
    sevenNineK4_part_{base}_{chunk:02d}_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
"""


def main() -> None:
    all_pairs = [old_pair_codes(base) for base in BASES]
    actual_counts = tuple(len(pairs) for pairs in all_pairs)
    expected_counts = tuple(count * CHUNK_WIDTH for count in BASE_CHUNK_COUNTS)
    if actual_counts != expected_counts:
        raise ValueError(
            f"unexpected old-pair counts {actual_counts}; expected {expected_counts}"
        )
    write_if_changed(
        LEAN / "P0054MiddleSevenNineK4Data.lean",
        render_data(all_pairs),
    )

    parts = [
        Part(base, chunk, part)
        for base, chunk_count in enumerate(BASE_CHUNK_COUNTS)
        for chunk in range(chunk_count)
        for part in range(PART_COUNT)
    ]
    lanes: list[list[Part]] = [[], []]
    for ordinal, spec in enumerate(parts):
        lane = lanes[ordinal % 2]
        previous = lane[-1] if lane else None
        write_if_changed(spec.path, render_part(spec, previous))
        lane.append(spec)

    previous_chunk: tuple[int, int] | None = None
    for base, chunk_count in enumerate(BASE_CHUNK_COUNTS):
        for chunk in range(chunk_count):
            write_if_changed(
                LEAN / f"P0054MiddleSevenNineK4Chunk{base}_{chunk:02d}.lean",
                render_chunk(base, chunk, previous_chunk),
            )
            previous_chunk = (base, chunk)

    roots = [lane[-1].module for lane in lanes]
    print(f"generated {sum(actual_counts)} checked old-pair data rows")
    print(f"generated {len(parts)} K4 part modules")
    print("part roots:")
    for root in roots:
        print(root)
    print(
        "chunk root: "
        f"AiMathLab.P0054MiddleSevenNineK4Chunk{previous_chunk[0]}_{previous_chunk[1]:02d}"
    )


if __name__ == "__main__":
    main()
