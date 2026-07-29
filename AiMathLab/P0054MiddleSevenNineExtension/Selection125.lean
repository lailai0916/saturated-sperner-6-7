import AiMathLab.P0054MiddleSevenNineExtension.Chunk125_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk125_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk125_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk125_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection121

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks125 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk125_00, sevenNineExtensionChunk125_01, sevenNineExtensionChunk125_02, sevenNineExtensionChunk125_03]

theorem sevenNineExtensionChunks125_flatten :
    sevenNineExtensionChunks125.flatMap id =
      middleFourListPowerset sevenNineExtensionVector125Eligible0 := by
  decide

theorem sevenNineExtensionChunks125_check :
    sevenNineExtensionChunks125.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector125
        sevenNineExtensionVector125Base0
        sevenNineExtensionVector125BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks125
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk125_00_check]
  rw [sevenNineExtensionChunk125_01_check]
  rw [sevenNineExtensionChunk125_02_check]
  rw [sevenNineExtensionChunk125_03_check]
  decide

theorem sevenNineExtensionVector125_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector125Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector125
        sevenNineExtensionVector125Base0
        sevenNineExtensionVector125BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks125_flatten
    sevenNineExtensionChunks125_check

theorem sevenNineExtensionVector125_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector125
      sevenNineExtensionVector125Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector125_base0 (by decide)
    sevenNineExtensionVector125_base_blocker0
    sevenNineExtensionVector125_eligible0
    sevenNineExtensionVector125_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
