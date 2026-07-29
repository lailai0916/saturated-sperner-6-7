import AiMathLab.P0054MiddleSevenNineExtension.Chunk121_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection119

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks121 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk121_00]

theorem sevenNineExtensionChunks121_flatten :
    sevenNineExtensionChunks121.flatMap id =
      middleFourListPowerset sevenNineExtensionVector121Eligible0 := by
  decide

theorem sevenNineExtensionChunks121_check :
    sevenNineExtensionChunks121.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector121
        sevenNineExtensionVector121Base0
        sevenNineExtensionVector121BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks121
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk121_00_check]


theorem sevenNineExtensionVector121_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector121Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector121
        sevenNineExtensionVector121Base0
        sevenNineExtensionVector121BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks121_flatten
    sevenNineExtensionChunks121_check

theorem sevenNineExtensionVector121_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector121
      sevenNineExtensionVector121Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector121_base0 (by decide)
    sevenNineExtensionVector121_base_blocker0
    sevenNineExtensionVector121_eligible0
    sevenNineExtensionVector121_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
