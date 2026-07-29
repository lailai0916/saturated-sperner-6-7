import AiMathLab.P0054MiddleSevenNineExtension.Chunk131_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk131_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk131_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk131_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection126

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks131 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk131_00, sevenNineExtensionChunk131_01, sevenNineExtensionChunk131_02, sevenNineExtensionChunk131_03]

theorem sevenNineExtensionChunks131_flatten :
    sevenNineExtensionChunks131.flatMap id =
      middleFourListPowerset sevenNineExtensionVector131Eligible0 := by
  decide

theorem sevenNineExtensionChunks131_check :
    sevenNineExtensionChunks131.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector131
        sevenNineExtensionVector131Base0
        sevenNineExtensionVector131BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks131
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk131_00_check]
  rw [sevenNineExtensionChunk131_01_check]
  rw [sevenNineExtensionChunk131_02_check]
  rw [sevenNineExtensionChunk131_03_check]
  decide

theorem sevenNineExtensionVector131_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector131Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector131
        sevenNineExtensionVector131Base0
        sevenNineExtensionVector131BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks131_flatten
    sevenNineExtensionChunks131_check

theorem sevenNineExtensionVector131_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector131
      sevenNineExtensionVector131Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector131_base0 (by decide)
    sevenNineExtensionVector131_base_blocker0
    sevenNineExtensionVector131_eligible0
    sevenNineExtensionVector131_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
