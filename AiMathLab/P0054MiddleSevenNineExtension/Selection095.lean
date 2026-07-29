import AiMathLab.P0054MiddleSevenNineExtension.Chunk095_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk095_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk095_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk095_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection092

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks095 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk095_00, sevenNineExtensionChunk095_01, sevenNineExtensionChunk095_02, sevenNineExtensionChunk095_03]

theorem sevenNineExtensionChunks095_flatten :
    sevenNineExtensionChunks095.flatMap id =
      middleFourListPowerset sevenNineExtensionVector095Eligible0 := by
  decide

theorem sevenNineExtensionChunks095_check :
    sevenNineExtensionChunks095.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector095
        sevenNineExtensionVector095Base0
        sevenNineExtensionVector095BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks095
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk095_00_check]
  rw [sevenNineExtensionChunk095_01_check]
  rw [sevenNineExtensionChunk095_02_check]
  rw [sevenNineExtensionChunk095_03_check]
  decide

theorem sevenNineExtensionVector095_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector095Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector095
        sevenNineExtensionVector095Base0
        sevenNineExtensionVector095BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks095_flatten
    sevenNineExtensionChunks095_check

theorem sevenNineExtensionVector095_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector095
      sevenNineExtensionVector095Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector095_base0 (by decide)
    sevenNineExtensionVector095_base_blocker0
    sevenNineExtensionVector095_eligible0
    sevenNineExtensionVector095_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
