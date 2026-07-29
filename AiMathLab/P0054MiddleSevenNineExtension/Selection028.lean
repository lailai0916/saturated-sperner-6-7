import AiMathLab.P0054MiddleSevenNineExtension.Chunk028_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk028_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk028_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk028_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection020

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks028 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk028_00, sevenNineExtensionChunk028_01, sevenNineExtensionChunk028_02, sevenNineExtensionChunk028_03]

theorem sevenNineExtensionChunks028_flatten :
    sevenNineExtensionChunks028.flatMap id =
      middleFourListPowerset sevenNineExtensionVector028Eligible0 := by
  decide

theorem sevenNineExtensionChunks028_check :
    sevenNineExtensionChunks028.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector028
        sevenNineExtensionVector028Base0
        sevenNineExtensionVector028BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks028
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk028_00_check]
  rw [sevenNineExtensionChunk028_01_check]
  rw [sevenNineExtensionChunk028_02_check]
  rw [sevenNineExtensionChunk028_03_check]
  decide

theorem sevenNineExtensionVector028_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector028Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector028
        sevenNineExtensionVector028Base0
        sevenNineExtensionVector028BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks028_flatten
    sevenNineExtensionChunks028_check

theorem sevenNineExtensionVector028_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector028
      sevenNineExtensionVector028Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector028_base0 (by decide)
    sevenNineExtensionVector028_base_blocker0
    sevenNineExtensionVector028_eligible0
    sevenNineExtensionVector028_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
