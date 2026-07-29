import AiMathLab.P0054MiddleSevenNineExtension.Chunk087_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection078

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks087 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk087_00]

theorem sevenNineExtensionChunks087_flatten :
    sevenNineExtensionChunks087.flatMap id =
      middleFourListPowerset sevenNineExtensionVector087Eligible0 := by
  decide

theorem sevenNineExtensionChunks087_check :
    sevenNineExtensionChunks087.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector087
        sevenNineExtensionVector087Base0
        sevenNineExtensionVector087BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks087
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk087_00_check]


theorem sevenNineExtensionVector087_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector087Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector087
        sevenNineExtensionVector087Base0
        sevenNineExtensionVector087BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks087_flatten
    sevenNineExtensionChunks087_check

theorem sevenNineExtensionVector087_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector087
      sevenNineExtensionVector087Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector087_base0 (by decide)
    sevenNineExtensionVector087_base_blocker0
    sevenNineExtensionVector087_eligible0
    sevenNineExtensionVector087_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
