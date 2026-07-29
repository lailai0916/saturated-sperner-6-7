import AiMathLab.P0054MiddleSevenNineExtension.Chunk064_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk064_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk064_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk064_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection060

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks064 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk064_00, sevenNineExtensionChunk064_01, sevenNineExtensionChunk064_02, sevenNineExtensionChunk064_03]

theorem sevenNineExtensionChunks064_flatten :
    sevenNineExtensionChunks064.flatMap id =
      middleFourListPowerset sevenNineExtensionVector064Eligible0 := by
  decide

theorem sevenNineExtensionChunks064_check :
    sevenNineExtensionChunks064.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector064
        sevenNineExtensionVector064Base0
        sevenNineExtensionVector064BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks064
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk064_00_check]
  rw [sevenNineExtensionChunk064_01_check]
  rw [sevenNineExtensionChunk064_02_check]
  rw [sevenNineExtensionChunk064_03_check]
  decide

theorem sevenNineExtensionVector064_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector064Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector064
        sevenNineExtensionVector064Base0
        sevenNineExtensionVector064BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks064_flatten
    sevenNineExtensionChunks064_check

theorem sevenNineExtensionVector064_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector064
      sevenNineExtensionVector064Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector064_base0 (by decide)
    sevenNineExtensionVector064_base_blocker0
    sevenNineExtensionVector064_eligible0
    sevenNineExtensionVector064_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
