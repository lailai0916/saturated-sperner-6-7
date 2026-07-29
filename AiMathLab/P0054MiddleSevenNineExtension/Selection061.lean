import AiMathLab.P0054MiddleSevenNineExtension.Chunk061_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk061_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk061_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk061_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection055

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks061 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk061_00, sevenNineExtensionChunk061_01, sevenNineExtensionChunk061_02, sevenNineExtensionChunk061_03]

theorem sevenNineExtensionChunks061_flatten :
    sevenNineExtensionChunks061.flatMap id =
      middleFourListPowerset sevenNineExtensionVector061Eligible0 := by
  decide

theorem sevenNineExtensionChunks061_check :
    sevenNineExtensionChunks061.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector061
        sevenNineExtensionVector061Base0
        sevenNineExtensionVector061BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks061
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk061_00_check]
  rw [sevenNineExtensionChunk061_01_check]
  rw [sevenNineExtensionChunk061_02_check]
  rw [sevenNineExtensionChunk061_03_check]
  decide

theorem sevenNineExtensionVector061_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector061Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector061
        sevenNineExtensionVector061Base0
        sevenNineExtensionVector061BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks061_flatten
    sevenNineExtensionChunks061_check

theorem sevenNineExtensionVector061_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector061
      sevenNineExtensionVector061Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector061_base0 (by decide)
    sevenNineExtensionVector061_base_blocker0
    sevenNineExtensionVector061_eligible0
    sevenNineExtensionVector061_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
