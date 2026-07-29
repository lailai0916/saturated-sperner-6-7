import AiMathLab.P0054MiddleSevenNineExtension.Chunk088_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection079

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks088 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk088_00]

theorem sevenNineExtensionChunks088_flatten :
    sevenNineExtensionChunks088.flatMap id =
      middleFourListPowerset sevenNineExtensionVector088Eligible0 := by
  decide

theorem sevenNineExtensionChunks088_check :
    sevenNineExtensionChunks088.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector088
        sevenNineExtensionVector088Base0
        sevenNineExtensionVector088BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks088
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk088_00_check]


theorem sevenNineExtensionVector088_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector088Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector088
        sevenNineExtensionVector088Base0
        sevenNineExtensionVector088BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks088_flatten
    sevenNineExtensionChunks088_check

theorem sevenNineExtensionVector088_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector088
      sevenNineExtensionVector088Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector088_base0 (by decide)
    sevenNineExtensionVector088_base_blocker0
    sevenNineExtensionVector088_eligible0
    sevenNineExtensionVector088_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
