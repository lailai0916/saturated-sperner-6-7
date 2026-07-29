import AiMathLab.P0054FanoAdjacentEightFiveChunk00
import AiMathLab.P0054FanoAdjacentEightFiveChunk01
import AiMathLab.P0054FanoAdjacentEightFiveChunk02
import AiMathLab.P0054FanoAdjacentEightFiveChunk03
import AiMathLab.P0054FanoAdjacentEightFiveChunk04
import AiMathLab.P0054FanoAdjacentEightFiveChunk05
import AiMathLab.P0054FanoAdjacentEightFiveChunk06
import AiMathLab.P0054FanoAdjacentEightFiveChunk07
import AiMathLab.P0054FanoAdjacentEightFiveChunk08
import AiMathLab.P0054FanoAdjacentEightFiveChunk09
import AiMathLab.P0054FanoAdjacentEightFiveChunk10
import AiMathLab.P0054FanoAdjacentEightFiveChunk11
import AiMathLab.P0054FanoAdjacentEightFiveChunk12
import AiMathLab.P0054FanoAdjacentEightFiveChunk13
import AiMathLab.P0054FanoAdjacentEightFiveChunk14
import AiMathLab.P0054FanoAdjacentEightFiveChunk15
import AiMathLab.P0054FanoAdjacentEightFiveChunk16
import AiMathLab.P0054FanoAdjacentEightFiveChunk17
import AiMathLab.P0054FanoAdjacentEightFiveChunk18
import AiMathLab.P0054FanoAdjacentEightFiveChunk19
import AiMathLab.P0054FanoAdjacentEightFiveChunk20
import AiMathLab.P0054FanoAdjacentEightFiveChunk21
import AiMathLab.P0054FanoAdjacentEightFiveChunk22
import AiMathLab.P0054FanoAdjacentEightFiveChunk23
import AiMathLab.P0054FanoAdjacentEightFiveChunk24
import AiMathLab.P0054FanoAdjacentEightFiveChunk25
import AiMathLab.P0054FanoAdjacentEightFiveChunk26

/-!
# Aggregated finite Fano certificate

The expensive propositions are checked in 27 independent kernel-reduction
modules.  This file only joins their consecutive list slices and preserves
the original public theorem interface.
-/

namespace AiMathLab.P0054.FanoAdjacentEightFiveFinite

open AiMathLab.P0054.FanoAdjacentSevenSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem fanoEightFiveCore_check : fanoEightFiveCoreCheck = true := by
  have hTail27 :
      (fanoSevenSixSelections.drop
        (27 * fanoSelectionChunkWidth)).all
          fanoEightFiveCoreSelectionCheck = true := by
    decide
  have hTail26 := fanoEightFiveAllDropOfChunk 26
    fanoEightFive_chunk_26_check
    (by simpa [fanoSelectionChunkWidth] using hTail27)
  have hTail25 := fanoEightFiveAllDropOfChunk 25
    fanoEightFive_chunk_25_check
    (by simpa [fanoSelectionChunkWidth] using hTail26)
  have hTail24 := fanoEightFiveAllDropOfChunk 24
    fanoEightFive_chunk_24_check
    (by simpa [fanoSelectionChunkWidth] using hTail25)
  have hTail23 := fanoEightFiveAllDropOfChunk 23
    fanoEightFive_chunk_23_check
    (by simpa [fanoSelectionChunkWidth] using hTail24)
  have hTail22 := fanoEightFiveAllDropOfChunk 22
    fanoEightFive_chunk_22_check
    (by simpa [fanoSelectionChunkWidth] using hTail23)
  have hTail21 := fanoEightFiveAllDropOfChunk 21
    fanoEightFive_chunk_21_check
    (by simpa [fanoSelectionChunkWidth] using hTail22)
  have hTail20 := fanoEightFiveAllDropOfChunk 20
    fanoEightFive_chunk_20_check
    (by simpa [fanoSelectionChunkWidth] using hTail21)
  have hTail19 := fanoEightFiveAllDropOfChunk 19
    fanoEightFive_chunk_19_check
    (by simpa [fanoSelectionChunkWidth] using hTail20)
  have hTail18 := fanoEightFiveAllDropOfChunk 18
    fanoEightFive_chunk_18_check
    (by simpa [fanoSelectionChunkWidth] using hTail19)
  have hTail17 := fanoEightFiveAllDropOfChunk 17
    fanoEightFive_chunk_17_check
    (by simpa [fanoSelectionChunkWidth] using hTail18)
  have hTail16 := fanoEightFiveAllDropOfChunk 16
    fanoEightFive_chunk_16_check
    (by simpa [fanoSelectionChunkWidth] using hTail17)
  have hTail15 := fanoEightFiveAllDropOfChunk 15
    fanoEightFive_chunk_15_check
    (by simpa [fanoSelectionChunkWidth] using hTail16)
  have hTail14 := fanoEightFiveAllDropOfChunk 14
    fanoEightFive_chunk_14_check
    (by simpa [fanoSelectionChunkWidth] using hTail15)
  have hTail13 := fanoEightFiveAllDropOfChunk 13
    fanoEightFive_chunk_13_check
    (by simpa [fanoSelectionChunkWidth] using hTail14)
  have hTail12 := fanoEightFiveAllDropOfChunk 12
    fanoEightFive_chunk_12_check
    (by simpa [fanoSelectionChunkWidth] using hTail13)
  have hTail11 := fanoEightFiveAllDropOfChunk 11
    fanoEightFive_chunk_11_check
    (by simpa [fanoSelectionChunkWidth] using hTail12)
  have hTail10 := fanoEightFiveAllDropOfChunk 10
    fanoEightFive_chunk_10_check
    (by simpa [fanoSelectionChunkWidth] using hTail11)
  have hTail09 := fanoEightFiveAllDropOfChunk 9
    fanoEightFive_chunk_09_check
    (by simpa [fanoSelectionChunkWidth] using hTail10)
  have hTail08 := fanoEightFiveAllDropOfChunk 8
    fanoEightFive_chunk_08_check
    (by simpa [fanoSelectionChunkWidth] using hTail09)
  have hTail07 := fanoEightFiveAllDropOfChunk 7
    fanoEightFive_chunk_07_check
    (by simpa [fanoSelectionChunkWidth] using hTail08)
  have hTail06 := fanoEightFiveAllDropOfChunk 6
    fanoEightFive_chunk_06_check
    (by simpa [fanoSelectionChunkWidth] using hTail07)
  have hTail05 := fanoEightFiveAllDropOfChunk 5
    fanoEightFive_chunk_05_check
    (by simpa [fanoSelectionChunkWidth] using hTail06)
  have hTail04 := fanoEightFiveAllDropOfChunk 4
    fanoEightFive_chunk_04_check
    (by simpa [fanoSelectionChunkWidth] using hTail05)
  have hTail03 := fanoEightFiveAllDropOfChunk 3
    fanoEightFive_chunk_03_check
    (by simpa [fanoSelectionChunkWidth] using hTail04)
  have hTail02 := fanoEightFiveAllDropOfChunk 2
    fanoEightFive_chunk_02_check
    (by simpa [fanoSelectionChunkWidth] using hTail03)
  have hTail01 := fanoEightFiveAllDropOfChunk 1
    fanoEightFive_chunk_01_check
    (by simpa [fanoSelectionChunkWidth] using hTail02)
  have hTail00 := fanoEightFiveAllDropOfChunk 0
    fanoEightFive_chunk_00_check
    (by simpa [fanoSelectionChunkWidth] using hTail01)
  simpa [fanoEightFiveCoreCheck] using hTail00

end AiMathLab.P0054.FanoAdjacentEightFiveFinite
