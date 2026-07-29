import AiMathLab.P0054MiddleSevenNineExtension.Chunk117_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection112

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks117 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk117_00]

theorem sevenNineExtensionChunks117_flatten :
    sevenNineExtensionChunks117.flatMap id =
      middleFourListPowerset sevenNineExtensionVector117Eligible0 := by
  decide

theorem sevenNineExtensionChunks117_check :
    sevenNineExtensionChunks117.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector117
        sevenNineExtensionVector117Base0
        sevenNineExtensionVector117BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks117
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk117_00_check]


theorem sevenNineExtensionVector117_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector117Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector117
        sevenNineExtensionVector117Base0
        sevenNineExtensionVector117BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks117_flatten
    sevenNineExtensionChunks117_check

theorem sevenNineExtensionVector117_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector117
      sevenNineExtensionVector117Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector117_base0 (by decide)
    sevenNineExtensionVector117_base_blocker0
    sevenNineExtensionVector117_eligible0
    sevenNineExtensionVector117_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
