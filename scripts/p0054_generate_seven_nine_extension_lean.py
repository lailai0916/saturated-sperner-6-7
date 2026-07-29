#!/usr/bin/env python3
"""Generate two-lane finite non-K4 extension checks for the 7+9 split."""

from __future__ import annotations

import ast
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FINITE = ROOT / "AiMathLab/P0054MiddleSevenNineFourFinite.lean"
OUTPUT = ROOT / "AiMathLab/P0054MiddleSevenNineExtension"
CHUNK_SIZE = 16


def certificate_values() -> list[list[int]]:
    lines = FINITE.read_text(encoding="utf-8").splitlines()
    start = lines.index("def middleFourMultiplicityCertificate : List (List Nat) :=")
    values: list[list[int]] = []
    for line in lines[start + 1 :]:
        stripped = line.strip().rstrip(",")
        if stripped == "]":
            break
        if stripped.startswith("[") and stripped != "[":
            value = ast.literal_eval(stripped)
            if not isinstance(value, list) or not all(isinstance(x, int) for x in value):
                raise TypeError("invalid certificate vector")
            values.append(value)
    if len(values) != 136:
        raise ValueError(f"expected 136 certificate vectors, found {len(values)}")
    return values


def minimize(rows: set[frozenset[int]]) -> tuple[frozenset[int], ...]:
    result: list[frozenset[int]] = []
    for row in sorted(rows, key=lambda current: (len(current), tuple(sorted(current)))):
        if not any(previous <= row for previous in result):
            result.append(row)
    return tuple(result)


def blockers(rows: tuple[frozenset[int], ...]) -> tuple[frozenset[int], ...]:
    candidates: tuple[frozenset[int], ...] = (frozenset(),)
    for row in rows:
        expanded: set[frozenset[int]] = set()
        for candidate in candidates:
            if candidate & row:
                expanded.add(candidate)
            else:
                expanded.update(candidate | {point} for point in row)
        candidates = minimize(expanded)
    return candidates


def list_powerset(values: list[int]) -> list[list[int]]:
    if not values:
        return [[]]
    tail = list_powerset(values[1:])
    return tail + [[values[0], *row] for row in tail]


@dataclass(frozen=True)
class VectorData:
    blocker_rows: list[frozenset[int]]
    selections: list[list[frozenset[int]]]
    bases: list[list[frozenset[int]]]
    eligible: list[list[int]]
    base_blockers: list[tuple[frozenset[int], ...]]


@dataclass(frozen=True)
class ChunkSpec:
    vector_index: int
    chunk_index: int
    rows: list[list[int]]


def extension_data(values: list[int]) -> VectorData:
    supports = [support for support, count in enumerate(values) for _ in range(count)]
    kernel = tuple(
        frozenset(
            point
            for point, support in enumerate(supports)
            if (support + 1) & (1 << row)
        )
        for row in range(4)
    )
    blocker_set = set(blockers(kernel))
    blocker_rows = [
        frozenset(row)
        for row in list_powerset(list(range(len(supports))))
        if frozenset(row) in blocker_set
    ]
    pair_rows = [row for row in blocker_rows if len(row) == 2]
    other_rows = [row for row in blocker_rows if len(row) != 2]
    selections = [
        [frozenset(row) for row in selection]
        for selection in list_powerset(other_rows)
        if len(selection) + len(pair_rows) <= 4
    ]
    center = len(supports)
    bases = [
        [
            row | {center} if len(row) == 2 or row in selection else row
            for row in blocker_rows
        ]
        for selection in selections
    ]
    eligible = [
        [
            point
            for point in range(center + 1)
            if sum(point in row for row in base) < 4
        ]
        for base in bases
    ]
    base_blockers = [blockers(tuple(base)) for base in bases]
    for base, dual in zip(bases, base_blockers, strict=True):
        base_card = len(set(base))
        if base_card not in {7, 8, 9}:
            raise ValueError(f"unexpected lift base size {base_card}")
        max_degree = max(
            (sum(point in row for row in base) for point in range(16)),
            default=0,
        )
        if base_card == 9 and max_degree <= 4 and len(dual) == 7:
            raise ValueError("nine-row candidate has blocker cardinality seven")
    return VectorData(blocker_rows, selections, bases, eligible, base_blockers)


def row_literal(row: frozenset[int]) -> str:
    if not row:
        return "∅"
    return "{" + ", ".join(str(value) for value in sorted(row)) + "}"


def rows_literal(rows: list[frozenset[int]] | tuple[frozenset[int], ...]) -> str:
    return "[" + ", ".join(row_literal(row) for row in rows) + "]"


def point_lists_literal(rows: list[list[int]]) -> str:
    return "[" + ", ".join(str(row) for row in rows) + "]"


def render_vector(index: int, values: list[int], data: VectorData) -> str:
    suffix = f"{index:03d}"
    previous = ""
    if index >= 2:
        previous = (
            f"import AiMathLab.P0054MiddleSevenNineExtension.Vector{index - 2:03d}\n"
        )
    selected_defs = "\n".join(
        f"""def sevenNineExtensionVector{suffix}Selected{selection_index} :
    List (G413.Row MiddleFourModelPoint) :=
  {rows_literal(selection)}
"""
        for selection_index, selection in enumerate(data.selections)
    )
    selection_constants = ", ".join(
        f"sevenNineExtensionVector{suffix}Selected{selection_index}"
        for selection_index in range(len(data.selections))
    )
    base_sections: list[str] = []
    for selection_index, base in enumerate(data.bases):
        base_card = len(set(base))
        section = f"""def sevenNineExtensionVector{suffix}Base{selection_index} :
    List (G413.Row MiddleFourModelPoint) :=
  {rows_literal(base)}

theorem sevenNineExtensionVector{suffix}_base{selection_index} :
    middleFourModelLiftBaseRows sevenNineExtensionVector{suffix}
        sevenNineExtensionVector{suffix}Selected{selection_index} =
      sevenNineExtensionVector{suffix}Base{selection_index} := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector{suffix}_blocker_rows]
  decide
"""
        if base_card == 8:
            section += f"""
def sevenNineExtensionVector{suffix}Eligible{selection_index} :
    List MiddleFourModelPoint :=
  {data.eligible[selection_index]}

def sevenNineExtensionVector{suffix}BaseBlocker{selection_index} :
    G413.Hypergraph MiddleFourModelPoint :=
  ({rows_literal(data.base_blockers[selection_index])}).toFinset

theorem sevenNineExtensionVector{suffix}_eligible{selection_index} :
    middleFourModelEligibleOldPointList sevenNineExtensionVector{suffix}
        sevenNineExtensionVector{suffix}Base{selection_index} =
      sevenNineExtensionVector{suffix}Eligible{selection_index} := by
  decide

theorem sevenNineExtensionVector{suffix}_base_blocker{selection_index} :
    fastBlocker sevenNineExtensionVector{suffix}Base{selection_index} =
      sevenNineExtensionVector{suffix}BaseBlocker{selection_index} := by
  decide
"""
        elif base_card == 9:
            final_card = len(data.base_blockers[selection_index])
            max_degree = max(
                (sum(point in row for row in base) for point in range(16)),
                default=0,
            )
            if max_degree <= 4:
                section += f"""
theorem sevenNineExtensionVector{suffix}_final_card{selection_index} :
    (fastBlocker sevenNineExtensionVector{suffix}Base{selection_index}).card =
      {final_card} := by
  decide

theorem sevenNineExtensionVector{suffix}_selection{selection_index}_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector{suffix}
      sevenNineExtensionVector{suffix}Selected{selection_index} = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector{suffix}_base{selection_index}, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector{suffix}Base{selection_index} = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector{suffix}Base{selection_index} = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector{suffix}_final_card{selection_index}]
  decide
"""
            else:
                section += f"""
theorem sevenNineExtensionVector{suffix}_selection{selection_index}_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector{suffix}
      sevenNineExtensionVector{suffix}Selected{selection_index} = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector{suffix}_base{selection_index}, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector{suffix}Base{selection_index} = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector{suffix}Base{selection_index} = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide
"""
        else:
            section += f"""
theorem sevenNineExtensionVector{suffix}_selection{selection_index}_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector{suffix}
      sevenNineExtensionVector{suffix}Selected{selection_index} = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector{suffix}_base{selection_index},
    if_neg (by decide), if_neg (by decide)]
"""
        base_sections.append(section)
    return f"""import AiMathLab.P0054MiddleSevenNineExtensionFinite
{previous}
namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector{suffix} : List Nat :=
  {values}

theorem sevenNineExtensionVector{suffix}_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD {index} [] =
      sevenNineExtensionVector{suffix} := by
  decide

def sevenNineExtensionVector{suffix}BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  {rows_literal(data.blocker_rows)}

{selected_defs}
def sevenNineExtensionVector{suffix}Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [{selection_constants}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector{suffix}_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector{suffix} =
      sevenNineExtensionVector{suffix}BlockerRows := by
  decide

theorem sevenNineExtensionVector{suffix}_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector{suffix} =
      sevenNineExtensionVector{suffix}Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector{suffix}_blocker_rows]
  decide

{"".join(base_sections)}
end AiMathLab.P0054.MiddleSevenNineExtensionFinite
"""


def render_chunk(spec: ChunkSpec, previous: ChunkSpec | None) -> str:
    suffix = f"{spec.vector_index:03d}"
    chunk_suffix = f"{spec.chunk_index:02d}"
    previous_import = ""
    if previous is not None:
        previous_import = (
            "import AiMathLab.P0054MiddleSevenNineExtension."
            f"Chunk{previous.vector_index:03d}_{previous.chunk_index:02d}\n"
        )
    return f"""import AiMathLab.P0054MiddleSevenNineExtension.Vector{suffix}
{previous_import}
namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk{suffix}_{chunk_suffix} :
    List (List MiddleFourModelPoint) :=
  {point_lists_literal(spec.rows)}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk{suffix}_{chunk_suffix}_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector{suffix}
        sevenNineExtensionVector{suffix}Base0
        sevenNineExtensionVector{suffix}BaseBlocker0
        sevenNineExtensionChunk{suffix}_{chunk_suffix} = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
"""


def render_selection(
    index: int, chunks: list[ChunkSpec], previous_index: int | None
) -> str:
    suffix = f"{index:03d}"
    imports = [
        "import AiMathLab.P0054MiddleSevenNineExtension."
        f"Chunk{index:03d}_{chunk.chunk_index:02d}"
        for chunk in chunks
    ]
    if previous_index is not None:
        imports.append(
            "import AiMathLab.P0054MiddleSevenNineExtension."
            f"Selection{previous_index:03d}"
        )
    chunk_constants = ", ".join(
        f"sevenNineExtensionChunk{suffix}_{chunk.chunk_index:02d}" for chunk in chunks
    )
    chunk_rewrites = "\n".join(
        f"  rw [sevenNineExtensionChunk{suffix}_{chunk.chunk_index:02d}_check]"
        for chunk in chunks
    )
    chunk_finish = "  decide" if len(chunks) > 1 else ""
    return f"""{chr(10).join(imports)}

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks{suffix} :
    List (List (List MiddleFourModelPoint)) :=
  [{chunk_constants}]

theorem sevenNineExtensionChunks{suffix}_flatten :
    sevenNineExtensionChunks{suffix}.flatMap id =
      middleFourListPowerset sevenNineExtensionVector{suffix}Eligible0 := by
  decide

theorem sevenNineExtensionChunks{suffix}_check :
    sevenNineExtensionChunks{suffix}.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector{suffix}
        sevenNineExtensionVector{suffix}Base0
        sevenNineExtensionVector{suffix}BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks{suffix}
  simp only [List.all_cons, List.all_nil, Bool.and_true]
{chunk_rewrites}
{chunk_finish}

theorem sevenNineExtensionVector{suffix}_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector{suffix}Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector{suffix}
        sevenNineExtensionVector{suffix}Base0
        sevenNineExtensionVector{suffix}BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks{suffix}_flatten
    sevenNineExtensionChunks{suffix}_check

theorem sevenNineExtensionVector{suffix}_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector{suffix}
      sevenNineExtensionVector{suffix}Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector{suffix}_base0 (by decide)
    sevenNineExtensionVector{suffix}_base_blocker0
    sevenNineExtensionVector{suffix}_eligible0
    sevenNineExtensionVector{suffix}_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
"""


def render_vector_check(index: int, selection_count: int, is_heavy: bool) -> str:
    suffix = f"{index:03d}"
    imports = [f"import AiMathLab.P0054MiddleSevenNineExtension.Vector{suffix}"]
    if is_heavy:
        imports.append(f"import AiMathLab.P0054MiddleSevenNineExtension.Selection{suffix}")
    if index >= 2:
        imports.append(
            f"import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck{index - 2:03d}"
        )
    rewrites = "\n".join(
        f"  rw [sevenNineExtensionVector{suffix}_selection{selection_index}_check]"
        for selection_index in range(selection_count)
    )
    finish = "  decide" if selection_count != 1 else ""
    return f"""{chr(10).join(imports)}

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector{suffix}_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector{suffix} = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector{suffix}_selections]
  unfold sevenNineExtensionVector{suffix}Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
{rewrites}
{finish}

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
"""


def render_aggregate(count: int) -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck{index:03d}"
        for index in (count - 2, count - 1)
    )
    local_checks = "\n".join(
        f"  have h{index:03d} := sevenNineExtensionVector{index:03d}_check\n"
        f"  simp only [sevenNineExtensionVector{index:03d}] at h{index:03d}"
        for index in range(count)
    )
    rewrites = "\n".join(f"  rw [h{index:03d}]" for index in range(count))
    return f"""{imports}

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionCertificateCheck_true :
    sevenNineExtensionCertificateCheck = true := by
{local_checks}
  unfold sevenNineExtensionCertificateCheck
    MiddleSevenNineFinite.middleFourMultiplicityCertificate
  simp only [List.all_cons, List.all_nil, Bool.and_true]
{rewrites}
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
"""


def write_if_changed(path: Path, content: str) -> None:
    if not path.exists() or path.read_text(encoding="utf-8") != content:
        path.write_text(content, encoding="utf-8")


def main() -> None:
    all_values = certificate_values()
    all_data = [extension_data(values) for values in all_values]
    OUTPUT.mkdir(parents=True, exist_ok=True)

    for index, (values, data) in enumerate(zip(all_values, all_data, strict=True)):
        write_if_changed(
            OUTPUT / f"Vector{index:03d}.lean", render_vector(index, values, data)
        )

    chunk_specs: list[ChunkSpec] = []
    chunks_by_vector: dict[int, list[ChunkSpec]] = {}
    heavy_indices: list[int] = []
    for index, data in enumerate(all_data):
        heavy_selections = [
            selection_index
            for selection_index, base in enumerate(data.bases)
            if len(set(base)) == 8
        ]
        if not heavy_selections:
            continue
        if heavy_selections != [0] or len(data.selections) != 1:
            raise ValueError(f"unexpected heavy selection shape at vector {index}")
        heavy_indices.append(index)
        old_subsets = list_powerset(data.eligible[0])
        chunks = [
            ChunkSpec(index, chunk_index, old_subsets[start : start + CHUNK_SIZE])
            for chunk_index, start in enumerate(range(0, len(old_subsets), CHUNK_SIZE))
        ]
        chunks_by_vector[index] = chunks
        chunk_specs.extend(chunks)

    chunk_lanes: list[list[ChunkSpec]] = [[], []]
    for ordinal, spec in enumerate(chunk_specs):
        lane = chunk_lanes[ordinal % 2]
        previous = lane[-1] if lane else None
        write_if_changed(
            OUTPUT / f"Chunk{spec.vector_index:03d}_{spec.chunk_index:02d}.lean",
            render_chunk(spec, previous),
        )
        lane.append(spec)

    selection_lanes: list[list[int]] = [[], []]
    for ordinal, index in enumerate(heavy_indices):
        lane = selection_lanes[ordinal % 2]
        previous = lane[-1] if lane else None
        write_if_changed(
            OUTPUT / f"Selection{index:03d}.lean",
            render_selection(index, chunks_by_vector[index], previous),
        )
        lane.append(index)

    for index, data in enumerate(all_data):
        write_if_changed(
            OUTPUT / f"VectorCheck{index:03d}.lean",
            render_vector_check(index, len(data.selections), index in chunks_by_vector),
        )

    write_if_changed(OUTPUT / "Check.lean", render_aggregate(len(all_values)))
    chunk_roots = [lane[-1] for lane in chunk_lanes]
    selection_roots = [lane[-1] for lane in selection_lanes]
    print(f"generated {len(all_values)} vector data modules")
    print(f"generated {len(chunk_specs)} extension chunks")
    print(
        "chunk roots: "
        + ", ".join(
            f"Chunk{spec.vector_index:03d}_{spec.chunk_index:02d}"
            for spec in chunk_roots
        )
    )
    print(
        "selection roots: "
        + ", ".join(f"Selection{index:03d}" for index in selection_roots)
    )


if __name__ == "__main__":
    main()
