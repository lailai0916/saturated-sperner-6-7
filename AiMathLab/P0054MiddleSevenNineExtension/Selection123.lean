import AiMathLab.P0054MiddleSevenNineExtension.Chunk123_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk123_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk123_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk123_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection120

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks123 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk123_00, sevenNineExtensionChunk123_01, sevenNineExtensionChunk123_02, sevenNineExtensionChunk123_03]

theorem sevenNineExtensionChunks123_flatten :
    sevenNineExtensionChunks123.flatMap id =
      middleFourListPowerset sevenNineExtensionVector123Eligible0 := by
  decide

theorem sevenNineExtensionChunks123_check :
    sevenNineExtensionChunks123.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector123
        sevenNineExtensionVector123Base0
        sevenNineExtensionVector123BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks123
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk123_00_check]
  rw [sevenNineExtensionChunk123_01_check]
  rw [sevenNineExtensionChunk123_02_check]
  rw [sevenNineExtensionChunk123_03_check]
  decide

theorem sevenNineExtensionVector123_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector123Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector123
        sevenNineExtensionVector123Base0
        sevenNineExtensionVector123BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks123_flatten
    sevenNineExtensionChunks123_check

theorem sevenNineExtensionVector123_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector123
      sevenNineExtensionVector123Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector123_base0 (by decide)
    sevenNineExtensionVector123_base_blocker0
    sevenNineExtensionVector123_eligible0
    sevenNineExtensionVector123_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
