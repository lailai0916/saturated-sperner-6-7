#!/usr/bin/env python3
"""Generate independent finite degree-four checks for the 49 certificates."""

from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FINITE = ROOT / "AiMathLab/P0054G420/MiddleFourFinite.lean"
OUTPUT = ROOT / "AiMathLab/P0054G420"
EXCEPTIONAL_INDEX = 20


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
    if len(values) != 49:
        raise ValueError(f"expected 49 certificate vectors, found {len(values)}")
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


def model_data(values: list[int]) -> tuple[list[frozenset[int]], list[frozenset[int]], int]:
    supports = [support for support, count in enumerate(values) for _ in range(count)]
    kernel = tuple(
        frozenset(point for point, support in enumerate(supports)
                  if (support + 1) & (1 << row))
        for row in range(4)
    )
    blocker_set = set(blockers(kernel))
    blocker_rows = [
        frozenset(row)
        for row in list_powerset(list(range(len(supports))))
        if frozenset(row) in blocker_set
    ]
    center = len(supports)
    candidate = [row | {center} if len(row) == 2 else row for row in blocker_rows]
    return blocker_rows, candidate, len(blockers(tuple(candidate)))


def exceptional_data(values: list[int]) -> tuple[
    list[frozenset[int]],
    list[list[frozenset[int]]],
    list[list[frozenset[int]]],
    list[list[int]],
]:
    supports = [support for support, count in enumerate(values) for _ in range(count)]
    kernel = tuple(
        frozenset(point for point, support in enumerate(supports)
                  if (support + 1) & (1 << row))
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
        selection for selection in list_powerset(other_rows)
        if len(selection) + len(pair_rows) <= 4
    ]
    center = len(supports)
    bases = [
        [row | {center} if len(row) == 2 or row in selection else row
         for row in blocker_rows]
        for selection in selections
    ]
    eligible = [
        [point for point in range(center + 1)
         if sum(point in row for row in base) < 4]
        for base in bases
    ]
    return blocker_rows, selections, bases, eligible


def row_literal(row: frozenset[int]) -> str:
    if not row:
        return "∅"
    return "{" + ", ".join(str(value) for value in sorted(row)) + "}"


def rows_literal(rows: list[frozenset[int]]) -> str:
    return "[" + ", ".join(row_literal(row) for row in rows) + "]"


def point_lists_literal(rows: list[list[int]]) -> str:
    return "[" + ", ".join(str(row) for row in rows) + "]"


def render(index: int, values: list[int]) -> str:
    suffix = f"{index:02d}"
    literal = str(values)
    check = ""
    if index == EXCEPTIONAL_INDEX:
        blocker_rows, selections, bases, eligible = exceptional_data(values)
        blocker_literal = rows_literal(blocker_rows)
        selection_literal = "[" + ", ".join(rows_literal(row) for row in selections) + "]"
        selection_defs = "\n".join(
            f"""def middleFourDegreeFourVector{suffix}Selected{selection_index} :
    List (G413.Row MiddleFourModelPoint) :=
  {rows_literal(selection)}

def middleFourDegreeFourVector{suffix}Base{selection_index} :
    List (G413.Row MiddleFourModelPoint) :=
  {rows_literal(bases[selection_index])}

def middleFourDegreeFourVector{suffix}Eligible{selection_index} :
    List MiddleFourModelPoint :=
  {eligible[selection_index]}

theorem middleFourDegreeFourVector{suffix}_base{selection_index} :
    middleFourModelLiftBaseRows middleFourDegreeFourVector{suffix}
        middleFourDegreeFourVector{suffix}Selected{selection_index} =
      middleFourDegreeFourVector{suffix}Base{selection_index} := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector{suffix}_blocker_rows]
  decide

theorem middleFourDegreeFourVector{suffix}_eligible{selection_index} :
    middleFourModelEligibleOldPointList middleFourDegreeFourVector{suffix}
        middleFourDegreeFourVector{suffix}Base{selection_index} =
      middleFourDegreeFourVector{suffix}Eligible{selection_index} := by
  decide
"""
            for selection_index, selection in enumerate(selections)
        )
        check = f"""
def middleFourDegreeFourVector{suffix}BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  {blocker_literal}

def middleFourDegreeFourVector{suffix}Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  {selection_literal}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector{suffix}_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector{suffix} =
      middleFourDegreeFourVector{suffix}BlockerRows := by
  decide

theorem middleFourDegreeFourVector{suffix}_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector{suffix} =
      middleFourDegreeFourVector{suffix}Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector{suffix}_blocker_rows]
  decide

{selection_defs}
"""
    else:
        blocker_rows, candidate, final_card = model_data(values)
        blocker_literal = rows_literal(blocker_rows)
        candidate_literal = rows_literal(candidate)
        check = f"""
def middleFourDegreeFourVector{suffix}BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  {blocker_literal}

def middleFourDegreeFourVector{suffix}Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  {candidate_literal}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector{suffix}_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector{suffix} =
      middleFourDegreeFourVector{suffix}BlockerRows := by
  decide

theorem middleFourDegreeFourVector{suffix}_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector{suffix} = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector{suffix}_blocker_rows]
  decide

theorem middleFourDegreeFourVector{suffix}_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector{suffix} [] =
      middleFourDegreeFourVector{suffix}Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector{suffix}_blocker_rows]
  decide

theorem middleFourDegreeFourVector{suffix}_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector{suffix} [] =
      [middleFourDegreeFourVector{suffix}Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector{suffix}_base]
  decide

theorem middleFourDegreeFourVector{suffix}_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector{suffix} =
      [middleFourDegreeFourVector{suffix}Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector{suffix}_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector{suffix}_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector{suffix}_final_card :
    (fastBlocker middleFourDegreeFourVector{suffix}Candidate).card =
      {final_card} := by
  decide

theorem middleFourDegreeFourVector{suffix}_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector{suffix} = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector{suffix}_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector{suffix}_final_card]
  decide
"""
    return f"""import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector{suffix} : List Nat :=
  {literal}

theorem middleFourDegreeFourVector{suffix}_certificate :
    middleFourMultiplicityCertificate.getD {index} [] =
      middleFourDegreeFourVector{suffix} := by
  decide
{check}
end AiMathLab.P0054.G420
"""


def render_chunk(
    values: list[int], selection_index: int, chunk_index: int,
    chunk: list[list[int]],
) -> str:
    suffix = f"{EXCEPTIONAL_INDEX:02d}"
    return f"""import AiMathLab.P0054G420.MiddleFourDegreeFourVector{suffix}

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector{suffix}Chunk{selection_index}_{chunk_index:02d} :
    List (List MiddleFourModelPoint) :=
  {point_lists_literal(chunk)}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector{suffix}_chunk{selection_index}_{chunk_index:02d}_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector{suffix}
        middleFourDegreeFourVector{suffix}Base{selection_index}
        middleFourDegreeFourVector{suffix}Chunk{selection_index}_{chunk_index:02d} = true := by
  decide

end AiMathLab.P0054.G420
"""


def render_selection(
    values: list[int], selection_index: int, chunks: list[list[list[int]]],
) -> str:
    suffix = f"{EXCEPTIONAL_INDEX:02d}"
    imports = "\n".join(
        f"import AiMathLab.P0054G420.MiddleFourDegreeFourVector{suffix}Chunk"
        f"{selection_index}_{chunk_index:02d}"
        for chunk_index in range(len(chunks))
    )
    chunk_constants = ", ".join(
        f"middleFourDegreeFourVector{suffix}Chunk{selection_index}_{chunk_index:02d}"
        for chunk_index in range(len(chunks))
    )
    chunk_rewrites = "\n".join(
        f"  rw [middleFourDegreeFourVector{suffix}_chunk"
        f"{selection_index}_{chunk_index:02d}_check]"
        for chunk_index in range(len(chunks))
    ) + "\n  decide"
    return f"""{imports}

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector{suffix}Chunks{selection_index} :
    List (List (List MiddleFourModelPoint)) :=
  [{chunk_constants}]

theorem middleFourDegreeFourVector{suffix}_chunks{selection_index}_flatten :
    middleFourDegreeFourVector{suffix}Chunks{selection_index}.flatMap id =
      middleFourListPowerset middleFourDegreeFourVector{suffix}Eligible{selection_index} := by
  decide

theorem middleFourDegreeFourVector{suffix}_chunks{selection_index}_check :
    middleFourDegreeFourVector{suffix}Chunks{selection_index}.all
      (middleFourModelRawChunkCheck middleFourDegreeFourVector{suffix}
        middleFourDegreeFourVector{suffix}Base{selection_index}) = true := by
  unfold middleFourDegreeFourVector{suffix}Chunks{selection_index}
  simp only [List.all_cons, List.all_nil, Bool.and_true]
{chunk_rewrites}

theorem middleFourDegreeFourVector{suffix}_raw{selection_index}_check :
    (middleFourListPowerset
      middleFourDegreeFourVector{suffix}Eligible{selection_index}).all
      (middleFourModelRawOldCheck middleFourDegreeFourVector{suffix}
        middleFourDegreeFourVector{suffix}Base{selection_index}) = true :=
  middleFourModelRawSelectionCheck_of_chunks _ _ _ _
    middleFourDegreeFourVector{suffix}_chunks{selection_index}_flatten
    middleFourDegreeFourVector{suffix}_chunks{selection_index}_check

theorem middleFourDegreeFourVector{suffix}_selection{selection_index}_check :
    (middleFourModelCandidateRowsForSelection middleFourDegreeFourVector{suffix}
      middleFourDegreeFourVector{suffix}Selected{selection_index}).all
      (fun candidate => decide ((fastBlocker candidate).card ≠ 8)) = true :=
  middleFourModelCandidateRowsForSelection_check_of_raw _ _ _ _
    middleFourDegreeFourVector{suffix}_base{selection_index} (by decide)
    middleFourDegreeFourVector{suffix}_eligible{selection_index}
    middleFourDegreeFourVector{suffix}_raw{selection_index}_check

end AiMathLab.P0054.G420
"""


def render_exceptional_check(selection_count: int) -> str:
    suffix = f"{EXCEPTIONAL_INDEX:02d}"
    imports = "\n".join(
        f"import AiMathLab.P0054G420.MiddleFourDegreeFourVector{suffix}Selection{index}"
        for index in range(selection_count)
    )
    local_checks = "\n".join(
        f"  have h{index} := middleFourDegreeFourVector{suffix}_selection{index}_check\n"
        f"  simp only [middleFourDegreeFourVector{suffix}Selected{index}] at h{index}"
        for index in range(selection_count)
    )
    conjunction = "\n".join(
        f"  rw [h{index}]" for index in range(selection_count)
    ) + "\n  decide"
    return f"""{imports}

namespace AiMathLab.P0054.G420

theorem middleFourDegreeFourVector{suffix}_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector{suffix} = true := by
{local_checks}
  unfold middleFourDegreeFourValuesCheck middleFourModelCandidateRows
  rw [middleFourDegreeFourVector{suffix}_selections]
  unfold middleFourDegreeFourVector{suffix}Selections
  simp only [List.flatMap_cons, List.flatMap_nil, List.all_append, List.all_nil,
    Bool.and_true]
{conjunction}

end AiMathLab.P0054.G420
"""


def write_if_changed(path: Path, content: str) -> None:
    if not path.exists() or path.read_text(encoding="utf-8") != content:
        path.write_text(content, encoding="utf-8")


def render_aggregate_check() -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054G420.MiddleFourDegreeFourVector{index:02d}"
        + ("Check" if index == EXCEPTIONAL_INDEX else "")
        for index in range(49)
    )
    local_checks = "\n".join(
        f"  have h{index:02d} := middleFourDegreeFourVector{index:02d}_check\n"
        f"  simp only [middleFourDegreeFourVector{index:02d}] at h{index:02d}"
        for index in range(49)
    )
    rewrites = "\n".join(f"  rw [h{index:02d}]" for index in range(49))
    return f"""{imports}

namespace AiMathLab.P0054.G420

theorem middleFourMultiplicityCertificate_degreeFour_check :
    middleFourMultiplicityCertificate.all middleFourDegreeFourValuesCheck = true := by
{local_checks}
  unfold middleFourMultiplicityCertificate
  simp only [List.all_cons, List.all_nil, Bool.and_true]
{rewrites}
  decide

end AiMathLab.P0054.G420
"""


def main() -> None:
    all_values = certificate_values()
    for index, values in enumerate(all_values):
        path = OUTPUT / f"MiddleFourDegreeFourVector{index:02d}.lean"
        write_if_changed(path, render(index, values))

    exceptional_values = all_values[EXCEPTIONAL_INDEX]
    _, selections, _, eligible = exceptional_data(exceptional_values)
    for selection_index, points in enumerate(eligible):
        old_subsets = list_powerset(points)
        chunk_size = 8 if selection_index == 0 else 4
        chunks = [old_subsets[index:index + chunk_size]
                  for index in range(0, len(old_subsets), chunk_size)]
        for chunk_index, chunk in enumerate(chunks):
            path = OUTPUT / (
                f"MiddleFourDegreeFourVector{EXCEPTIONAL_INDEX:02d}Chunk"
                f"{selection_index}_{chunk_index:02d}.lean"
            )
            write_if_changed(
                path,
                render_chunk(exceptional_values, selection_index, chunk_index, chunk),
            )
        selection_path = OUTPUT / (
            f"MiddleFourDegreeFourVector{EXCEPTIONAL_INDEX:02d}Selection"
            f"{selection_index}.lean"
        )
        write_if_changed(
            selection_path,
            render_selection(exceptional_values, selection_index, chunks),
        )
    check_path = OUTPUT / (
        f"MiddleFourDegreeFourVector{EXCEPTIONAL_INDEX:02d}Check.lean"
    )
    write_if_changed(check_path, render_exceptional_check(len(selections)))
    write_if_changed(
        OUTPUT / "MiddleFourDegreeFourCheck.lean",
        render_aggregate_check(),
    )


if __name__ == "__main__":
    main()
