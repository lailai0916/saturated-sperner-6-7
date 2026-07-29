import AiMathLab.P0054MiddleSevenNineExtension.Chunk079_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk079_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk079_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk079_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection073

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks079 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk079_00, sevenNineExtensionChunk079_01, sevenNineExtensionChunk079_02, sevenNineExtensionChunk079_03]

theorem sevenNineExtensionChunks079_flatten :
    sevenNineExtensionChunks079.flatMap id =
      middleFourListPowerset sevenNineExtensionVector079Eligible0 := by
  decide

theorem sevenNineExtensionChunks079_check :
    sevenNineExtensionChunks079.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector079
        sevenNineExtensionVector079Base0
        sevenNineExtensionVector079BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks079
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk079_00_check]
  rw [sevenNineExtensionChunk079_01_check]
  rw [sevenNineExtensionChunk079_02_check]
  rw [sevenNineExtensionChunk079_03_check]
  decide

theorem sevenNineExtensionVector079_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector079Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector079
        sevenNineExtensionVector079Base0
        sevenNineExtensionVector079BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks079_flatten
    sevenNineExtensionChunks079_check

theorem sevenNineExtensionVector079_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector079
      sevenNineExtensionVector079Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector079_base0 (by decide)
    sevenNineExtensionVector079_base_blocker0
    sevenNineExtensionVector079_eligible0
    sevenNineExtensionVector079_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
