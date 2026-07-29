import AiMathLab.P0054MiddleSevenNineExtension.Chunk046_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk046_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk046_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk046_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection032

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks046 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk046_00, sevenNineExtensionChunk046_01, sevenNineExtensionChunk046_02, sevenNineExtensionChunk046_03]

theorem sevenNineExtensionChunks046_flatten :
    sevenNineExtensionChunks046.flatMap id =
      middleFourListPowerset sevenNineExtensionVector046Eligible0 := by
  decide

theorem sevenNineExtensionChunks046_check :
    sevenNineExtensionChunks046.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector046
        sevenNineExtensionVector046Base0
        sevenNineExtensionVector046BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks046
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk046_00_check]
  rw [sevenNineExtensionChunk046_01_check]
  rw [sevenNineExtensionChunk046_02_check]
  rw [sevenNineExtensionChunk046_03_check]
  decide

theorem sevenNineExtensionVector046_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector046Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector046
        sevenNineExtensionVector046Base0
        sevenNineExtensionVector046BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks046_flatten
    sevenNineExtensionChunks046_check

theorem sevenNineExtensionVector046_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector046
      sevenNineExtensionVector046Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector046_base0 (by decide)
    sevenNineExtensionVector046_base_blocker0
    sevenNineExtensionVector046_eligible0
    sevenNineExtensionVector046_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
