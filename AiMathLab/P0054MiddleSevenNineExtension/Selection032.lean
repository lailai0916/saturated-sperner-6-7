import AiMathLab.P0054MiddleSevenNineExtension.Chunk032_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk032_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk032_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk032_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection028

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks032 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk032_00, sevenNineExtensionChunk032_01, sevenNineExtensionChunk032_02, sevenNineExtensionChunk032_03]

theorem sevenNineExtensionChunks032_flatten :
    sevenNineExtensionChunks032.flatMap id =
      middleFourListPowerset sevenNineExtensionVector032Eligible0 := by
  decide

theorem sevenNineExtensionChunks032_check :
    sevenNineExtensionChunks032.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector032
        sevenNineExtensionVector032Base0
        sevenNineExtensionVector032BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks032
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk032_00_check]
  rw [sevenNineExtensionChunk032_01_check]
  rw [sevenNineExtensionChunk032_02_check]
  rw [sevenNineExtensionChunk032_03_check]
  decide

theorem sevenNineExtensionVector032_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector032Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector032
        sevenNineExtensionVector032Base0
        sevenNineExtensionVector032BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks032_flatten
    sevenNineExtensionChunks032_check

theorem sevenNineExtensionVector032_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector032
      sevenNineExtensionVector032Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector032_base0 (by decide)
    sevenNineExtensionVector032_base_blocker0
    sevenNineExtensionVector032_eligible0
    sevenNineExtensionVector032_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
