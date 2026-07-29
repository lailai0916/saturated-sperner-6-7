import AiMathLab.P0054MiddleSevenNineExtension.Chunk129_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk129_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk129_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk129_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection125

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks129 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk129_00, sevenNineExtensionChunk129_01, sevenNineExtensionChunk129_02, sevenNineExtensionChunk129_03]

theorem sevenNineExtensionChunks129_flatten :
    sevenNineExtensionChunks129.flatMap id =
      middleFourListPowerset sevenNineExtensionVector129Eligible0 := by
  decide

theorem sevenNineExtensionChunks129_check :
    sevenNineExtensionChunks129.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector129
        sevenNineExtensionVector129Base0
        sevenNineExtensionVector129BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks129
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk129_00_check]
  rw [sevenNineExtensionChunk129_01_check]
  rw [sevenNineExtensionChunk129_02_check]
  rw [sevenNineExtensionChunk129_03_check]
  decide

theorem sevenNineExtensionVector129_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector129Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector129
        sevenNineExtensionVector129Base0
        sevenNineExtensionVector129BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks129_flatten
    sevenNineExtensionChunks129_check

theorem sevenNineExtensionVector129_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector129
      sevenNineExtensionVector129Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector129_base0 (by decide)
    sevenNineExtensionVector129_base_blocker0
    sevenNineExtensionVector129_eligible0
    sevenNineExtensionVector129_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
