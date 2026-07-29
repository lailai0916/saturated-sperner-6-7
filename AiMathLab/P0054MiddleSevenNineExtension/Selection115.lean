import AiMathLab.P0054MiddleSevenNineExtension.Chunk115_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk115_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk115_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk115_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection109

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks115 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk115_00, sevenNineExtensionChunk115_01, sevenNineExtensionChunk115_02, sevenNineExtensionChunk115_03]

theorem sevenNineExtensionChunks115_flatten :
    sevenNineExtensionChunks115.flatMap id =
      middleFourListPowerset sevenNineExtensionVector115Eligible0 := by
  decide

theorem sevenNineExtensionChunks115_check :
    sevenNineExtensionChunks115.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector115
        sevenNineExtensionVector115Base0
        sevenNineExtensionVector115BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks115
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk115_00_check]
  rw [sevenNineExtensionChunk115_01_check]
  rw [sevenNineExtensionChunk115_02_check]
  rw [sevenNineExtensionChunk115_03_check]
  decide

theorem sevenNineExtensionVector115_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector115Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector115
        sevenNineExtensionVector115Base0
        sevenNineExtensionVector115BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks115_flatten
    sevenNineExtensionChunks115_check

theorem sevenNineExtensionVector115_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector115
      sevenNineExtensionVector115Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector115_base0 (by decide)
    sevenNineExtensionVector115_base_blocker0
    sevenNineExtensionVector115_eligible0
    sevenNineExtensionVector115_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
