import AiMathLab.P0054MiddleSevenNineExtension.Chunk106_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection104

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks106 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk106_00]

theorem sevenNineExtensionChunks106_flatten :
    sevenNineExtensionChunks106.flatMap id =
      middleFourListPowerset sevenNineExtensionVector106Eligible0 := by
  decide

theorem sevenNineExtensionChunks106_check :
    sevenNineExtensionChunks106.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector106
        sevenNineExtensionVector106Base0
        sevenNineExtensionVector106BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks106
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk106_00_check]


theorem sevenNineExtensionVector106_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector106Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector106
        sevenNineExtensionVector106Base0
        sevenNineExtensionVector106BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks106_flatten
    sevenNineExtensionChunks106_check

theorem sevenNineExtensionVector106_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector106
      sevenNineExtensionVector106Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector106_base0 (by decide)
    sevenNineExtensionVector106_base_blocker0
    sevenNineExtensionVector106_eligible0
    sevenNineExtensionVector106_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
