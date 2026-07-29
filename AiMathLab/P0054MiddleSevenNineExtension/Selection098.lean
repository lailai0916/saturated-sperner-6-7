import AiMathLab.P0054MiddleSevenNineExtension.Chunk098_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk098_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk098_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk098_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection095

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks098 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk098_00, sevenNineExtensionChunk098_01, sevenNineExtensionChunk098_02, sevenNineExtensionChunk098_03]

theorem sevenNineExtensionChunks098_flatten :
    sevenNineExtensionChunks098.flatMap id =
      middleFourListPowerset sevenNineExtensionVector098Eligible0 := by
  decide

theorem sevenNineExtensionChunks098_check :
    sevenNineExtensionChunks098.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector098
        sevenNineExtensionVector098Base0
        sevenNineExtensionVector098BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks098
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk098_00_check]
  rw [sevenNineExtensionChunk098_01_check]
  rw [sevenNineExtensionChunk098_02_check]
  rw [sevenNineExtensionChunk098_03_check]
  decide

theorem sevenNineExtensionVector098_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector098Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector098
        sevenNineExtensionVector098Base0
        sevenNineExtensionVector098BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks098_flatten
    sevenNineExtensionChunks098_check

theorem sevenNineExtensionVector098_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector098
      sevenNineExtensionVector098Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector098_base0 (by decide)
    sevenNineExtensionVector098_base_blocker0
    sevenNineExtensionVector098_eligible0
    sevenNineExtensionVector098_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
