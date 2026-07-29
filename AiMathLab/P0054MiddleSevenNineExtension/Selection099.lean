import AiMathLab.P0054MiddleSevenNineExtension.Chunk099_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection096

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks099 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk099_00]

theorem sevenNineExtensionChunks099_flatten :
    sevenNineExtensionChunks099.flatMap id =
      middleFourListPowerset sevenNineExtensionVector099Eligible0 := by
  decide

theorem sevenNineExtensionChunks099_check :
    sevenNineExtensionChunks099.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector099
        sevenNineExtensionVector099Base0
        sevenNineExtensionVector099BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks099
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk099_00_check]


theorem sevenNineExtensionVector099_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector099Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector099
        sevenNineExtensionVector099Base0
        sevenNineExtensionVector099BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks099_flatten
    sevenNineExtensionChunks099_check

theorem sevenNineExtensionVector099_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector099
      sevenNineExtensionVector099Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector099_base0 (by decide)
    sevenNineExtensionVector099_base_blocker0
    sevenNineExtensionVector099_eligible0
    sevenNineExtensionVector099_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
