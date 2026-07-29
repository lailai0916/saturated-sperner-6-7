import AiMathLab.P0054FanoAdjacentSevenSixChunk26

/-!
# Aggregated finite Fano certificate

The expensive propositions are checked in 27 independent kernel-reduction
modules.  This file only joins their consecutive list slices and preserves
the original public theorem interface.
-/

namespace AiMathLab.P0054.FanoAdjacentSevenSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem fanoSevenSix_check : fanoSevenSixCheck = true := by
  have hTail27 :
      (fanoSevenSixSelections.drop
        (27 * fanoSelectionChunkWidth)).all
          fanoSevenSixSelectionCheck = true := by
    decide
  have hTail26 := fanoSevenSixAllDropOfChunk 26
    fanoSevenSix_chunk_26_check
    (by simpa [fanoSelectionChunkWidth] using hTail27)
  have hTail25 := fanoSevenSixAllDropOfChunk 25
    fanoSevenSix_chunk_25_check
    (by simpa [fanoSelectionChunkWidth] using hTail26)
  have hTail24 := fanoSevenSixAllDropOfChunk 24
    fanoSevenSix_chunk_24_check
    (by simpa [fanoSelectionChunkWidth] using hTail25)
  have hTail23 := fanoSevenSixAllDropOfChunk 23
    fanoSevenSix_chunk_23_check
    (by simpa [fanoSelectionChunkWidth] using hTail24)
  have hTail22 := fanoSevenSixAllDropOfChunk 22
    fanoSevenSix_chunk_22_check
    (by simpa [fanoSelectionChunkWidth] using hTail23)
  have hTail21 := fanoSevenSixAllDropOfChunk 21
    fanoSevenSix_chunk_21_check
    (by simpa [fanoSelectionChunkWidth] using hTail22)
  have hTail20 := fanoSevenSixAllDropOfChunk 20
    fanoSevenSix_chunk_20_check
    (by simpa [fanoSelectionChunkWidth] using hTail21)
  have hTail19 := fanoSevenSixAllDropOfChunk 19
    fanoSevenSix_chunk_19_check
    (by simpa [fanoSelectionChunkWidth] using hTail20)
  have hTail18 := fanoSevenSixAllDropOfChunk 18
    fanoSevenSix_chunk_18_check
    (by simpa [fanoSelectionChunkWidth] using hTail19)
  have hTail17 := fanoSevenSixAllDropOfChunk 17
    fanoSevenSix_chunk_17_check
    (by simpa [fanoSelectionChunkWidth] using hTail18)
  have hTail16 := fanoSevenSixAllDropOfChunk 16
    fanoSevenSix_chunk_16_check
    (by simpa [fanoSelectionChunkWidth] using hTail17)
  have hTail15 := fanoSevenSixAllDropOfChunk 15
    fanoSevenSix_chunk_15_check
    (by simpa [fanoSelectionChunkWidth] using hTail16)
  have hTail14 := fanoSevenSixAllDropOfChunk 14
    fanoSevenSix_chunk_14_check
    (by simpa [fanoSelectionChunkWidth] using hTail15)
  have hTail13 := fanoSevenSixAllDropOfChunk 13
    fanoSevenSix_chunk_13_check
    (by simpa [fanoSelectionChunkWidth] using hTail14)
  have hTail12 := fanoSevenSixAllDropOfChunk 12
    fanoSevenSix_chunk_12_check
    (by simpa [fanoSelectionChunkWidth] using hTail13)
  have hTail11 := fanoSevenSixAllDropOfChunk 11
    fanoSevenSix_chunk_11_check
    (by simpa [fanoSelectionChunkWidth] using hTail12)
  have hTail10 := fanoSevenSixAllDropOfChunk 10
    fanoSevenSix_chunk_10_check
    (by simpa [fanoSelectionChunkWidth] using hTail11)
  have hTail09 := fanoSevenSixAllDropOfChunk 9
    fanoSevenSix_chunk_09_check
    (by simpa [fanoSelectionChunkWidth] using hTail10)
  have hTail08 := fanoSevenSixAllDropOfChunk 8
    fanoSevenSix_chunk_08_check
    (by simpa [fanoSelectionChunkWidth] using hTail09)
  have hTail07 := fanoSevenSixAllDropOfChunk 7
    fanoSevenSix_chunk_07_check
    (by simpa [fanoSelectionChunkWidth] using hTail08)
  have hTail06 := fanoSevenSixAllDropOfChunk 6
    fanoSevenSix_chunk_06_check
    (by simpa [fanoSelectionChunkWidth] using hTail07)
  have hTail05 := fanoSevenSixAllDropOfChunk 5
    fanoSevenSix_chunk_05_check
    (by simpa [fanoSelectionChunkWidth] using hTail06)
  have hTail04 := fanoSevenSixAllDropOfChunk 4
    fanoSevenSix_chunk_04_check
    (by simpa [fanoSelectionChunkWidth] using hTail05)
  have hTail03 := fanoSevenSixAllDropOfChunk 3
    fanoSevenSix_chunk_03_check
    (by simpa [fanoSelectionChunkWidth] using hTail04)
  have hTail02 := fanoSevenSixAllDropOfChunk 2
    fanoSevenSix_chunk_02_check
    (by simpa [fanoSelectionChunkWidth] using hTail03)
  have hTail01 := fanoSevenSixAllDropOfChunk 1
    fanoSevenSix_chunk_01_check
    (by simpa [fanoSelectionChunkWidth] using hTail02)
  have hTail00 := fanoSevenSixAllDropOfChunk 0
    fanoSevenSix_chunk_00_check
    (by simpa [fanoSelectionChunkWidth] using hTail01)
  simpa [fanoSevenSixCheck] using hTail00

end AiMathLab.P0054.FanoAdjacentSevenSixFinite
