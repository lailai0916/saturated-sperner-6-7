#!/usr/bin/env python3
"""Generate single-lane finite certificate chunks for the Fano branches."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "AiMathLab"
CHUNK_COUNT = 27


def write_if_changed(path: Path, content: str) -> None:
    if not path.exists() or path.read_text(encoding="utf-8") != content:
        path.write_text(content, encoding="utf-8")


def render_chunk(kind: str, index: int) -> str:
    if kind == "SevenSix":
        namespace = "AiMathLab.P0054.FanoAdjacentSevenSixFinite"
        core = "AiMathLab.P0054FanoAdjacentSevenSixFiniteCore"
        stem = "AiMathLab.P0054FanoAdjacentSevenSixChunk"
        check = "fanoSevenSixChunkCheck"
        theorem = "fanoSevenSix_chunk"
    elif kind == "EightFive":
        namespace = "AiMathLab.P0054.FanoAdjacentEightFiveFinite"
        core = "AiMathLab.P0054FanoAdjacentEightFiveFiniteCore"
        stem = "AiMathLab.P0054FanoAdjacentEightFiveChunk"
        check = "fanoEightFiveCoreChunkCheck"
        theorem = "fanoEightFive_chunk"
    else:
        raise ValueError(f"unknown certificate kind: {kind}")
    imported = core if index == 0 else f"{stem}{index - 1:02d}"
    return f"""import {imported}

namespace {namespace}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks one block of 81 labelled Fano selections.
theorem {theorem}_{index:02d}_check :
    {check} {index} = true := by
  decide

end {namespace}
"""


def render_aggregate(kind: str) -> str:
    if kind == "SevenSix":
        namespace = "AiMathLab.P0054.FanoAdjacentSevenSixFinite"
        root = "AiMathLab.P0054FanoAdjacentSevenSixChunk26"
        predicate = "fanoSevenSixSelectionCheck"
        chunk_theorem = "fanoSevenSix_chunk"
        step = "fanoSevenSixAllDropOfChunk"
        check = "fanoSevenSixCheck"
        theorem = "fanoSevenSix_check"
    elif kind == "EightFive":
        namespace = "AiMathLab.P0054.FanoAdjacentEightFiveFinite"
        root = "AiMathLab.P0054FanoAdjacentEightFiveChunk26"
        predicate = "fanoEightFiveCoreSelectionCheck"
        chunk_theorem = "fanoEightFive_chunk"
        step = "fanoEightFiveAllDropOfChunk"
        check = "fanoEightFiveCoreCheck"
        theorem = "fanoEightFiveCore_check"
    else:
        raise ValueError(f"unknown certificate kind: {kind}")

    tail_steps: list[str] = []
    for index in reversed(range(CHUNK_COUNT)):
        tail_steps.append(
            f"  have hTail{index:02d} := {step} {index}\n"
            f"    {chunk_theorem}_{index:02d}_check\n"
            f"    (by simpa [fanoSelectionChunkWidth] using hTail{index + 1:02d})"
        )
    steps = "\n".join(tail_steps)
    return f"""import {root}

/-!
# Aggregated finite Fano certificate

The expensive propositions are checked in 27 independent kernel-reduction
modules.  This file only joins their consecutive list slices and preserves
the original public theorem interface.
-/

namespace {namespace}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem {theorem} : {check} = true := by
  have hTail27 :
      (fanoSevenSixSelections.drop
        (27 * fanoSelectionChunkWidth)).all
          {predicate} = true := by
    decide
{steps}
  simpa [{check}] using hTail00

end {namespace}
"""


def main() -> None:
    for kind in ("SevenSix", "EightFive"):
        for index in range(CHUNK_COUNT):
            write_if_changed(
                LEAN / f"P0054FanoAdjacent{kind}Chunk{index:02d}.lean",
                render_chunk(kind, index),
            )
        write_if_changed(
            LEAN / f"P0054FanoAdjacent{kind}Finite.lean",
            render_aggregate(kind),
        )
    print("generated 27 SevenSix chunks and 27 EightFive chunks")


if __name__ == "__main__":
    main()
