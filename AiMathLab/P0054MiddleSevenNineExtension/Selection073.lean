import AiMathLab.P0054MiddleSevenNineExtension.Chunk073_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk073_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk073_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk073_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection065

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks073 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk073_00, sevenNineExtensionChunk073_01, sevenNineExtensionChunk073_02, sevenNineExtensionChunk073_03]

theorem sevenNineExtensionChunks073_flatten :
    sevenNineExtensionChunks073.flatMap id =
      middleFourListPowerset sevenNineExtensionVector073Eligible0 := by
  decide

theorem sevenNineExtensionChunks073_check :
    sevenNineExtensionChunks073.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector073
        sevenNineExtensionVector073Base0
        sevenNineExtensionVector073BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks073
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk073_00_check]
  rw [sevenNineExtensionChunk073_01_check]
  rw [sevenNineExtensionChunk073_02_check]
  rw [sevenNineExtensionChunk073_03_check]
  decide

theorem sevenNineExtensionVector073_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector073Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector073
        sevenNineExtensionVector073Base0
        sevenNineExtensionVector073BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks073_flatten
    sevenNineExtensionChunks073_check

theorem sevenNineExtensionVector073_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector073
      sevenNineExtensionVector073Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector073_base0 (by decide)
    sevenNineExtensionVector073_base_blocker0
    sevenNineExtensionVector073_eligible0
    sevenNineExtensionVector073_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
