import AiMathLab.P0054MiddleSevenNineExtension.Chunk096_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection093

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks096 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk096_00]

theorem sevenNineExtensionChunks096_flatten :
    sevenNineExtensionChunks096.flatMap id =
      middleFourListPowerset sevenNineExtensionVector096Eligible0 := by
  decide

theorem sevenNineExtensionChunks096_check :
    sevenNineExtensionChunks096.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector096
        sevenNineExtensionVector096Base0
        sevenNineExtensionVector096BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks096
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk096_00_check]


theorem sevenNineExtensionVector096_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector096Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector096
        sevenNineExtensionVector096Base0
        sevenNineExtensionVector096BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks096_flatten
    sevenNineExtensionChunks096_check

theorem sevenNineExtensionVector096_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector096
      sevenNineExtensionVector096Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector096_base0 (by decide)
    sevenNineExtensionVector096_base_blocker0
    sevenNineExtensionVector096_eligible0
    sevenNineExtensionVector096_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
