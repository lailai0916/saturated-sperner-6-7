import AiMathLab.P0054MiddleSevenNineExtension.Chunk126_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection123

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks126 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk126_00]

theorem sevenNineExtensionChunks126_flatten :
    sevenNineExtensionChunks126.flatMap id =
      middleFourListPowerset sevenNineExtensionVector126Eligible0 := by
  decide

theorem sevenNineExtensionChunks126_check :
    sevenNineExtensionChunks126.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector126
        sevenNineExtensionVector126Base0
        sevenNineExtensionVector126BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks126
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk126_00_check]


theorem sevenNineExtensionVector126_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector126Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector126
        sevenNineExtensionVector126Base0
        sevenNineExtensionVector126BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks126_flatten
    sevenNineExtensionChunks126_check

theorem sevenNineExtensionVector126_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector126
      sevenNineExtensionVector126Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector126_base0 (by decide)
    sevenNineExtensionVector126_base_blocker0
    sevenNineExtensionVector126_eligible0
    sevenNineExtensionVector126_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
