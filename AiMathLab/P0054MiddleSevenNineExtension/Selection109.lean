import AiMathLab.P0054MiddleSevenNineExtension.Chunk109_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection106

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks109 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk109_00]

theorem sevenNineExtensionChunks109_flatten :
    sevenNineExtensionChunks109.flatMap id =
      middleFourListPowerset sevenNineExtensionVector109Eligible0 := by
  decide

theorem sevenNineExtensionChunks109_check :
    sevenNineExtensionChunks109.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector109
        sevenNineExtensionVector109Base0
        sevenNineExtensionVector109BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks109
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk109_00_check]


theorem sevenNineExtensionVector109_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector109Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector109
        sevenNineExtensionVector109Base0
        sevenNineExtensionVector109BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks109_flatten
    sevenNineExtensionChunks109_check

theorem sevenNineExtensionVector109_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector109
      sevenNineExtensionVector109Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector109_base0 (by decide)
    sevenNineExtensionVector109_base_blocker0
    sevenNineExtensionVector109_eligible0
    sevenNineExtensionVector109_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
