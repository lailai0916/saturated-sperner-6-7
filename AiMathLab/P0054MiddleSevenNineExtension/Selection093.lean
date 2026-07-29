import AiMathLab.P0054MiddleSevenNineExtension.Chunk093_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection091

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks093 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk093_00]

theorem sevenNineExtensionChunks093_flatten :
    sevenNineExtensionChunks093.flatMap id =
      middleFourListPowerset sevenNineExtensionVector093Eligible0 := by
  decide

theorem sevenNineExtensionChunks093_check :
    sevenNineExtensionChunks093.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector093
        sevenNineExtensionVector093Base0
        sevenNineExtensionVector093BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks093
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk093_00_check]


theorem sevenNineExtensionVector093_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector093Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector093
        sevenNineExtensionVector093Base0
        sevenNineExtensionVector093BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks093_flatten
    sevenNineExtensionChunks093_check

theorem sevenNineExtensionVector093_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector093
      sevenNineExtensionVector093Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector093_base0 (by decide)
    sevenNineExtensionVector093_base_blocker0
    sevenNineExtensionVector093_eligible0
    sevenNineExtensionVector093_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
