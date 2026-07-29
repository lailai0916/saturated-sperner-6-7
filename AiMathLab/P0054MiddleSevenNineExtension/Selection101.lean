import AiMathLab.P0054MiddleSevenNineExtension.Chunk101_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk101_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk101_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk101_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection098

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks101 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk101_00, sevenNineExtensionChunk101_01, sevenNineExtensionChunk101_02, sevenNineExtensionChunk101_03]

theorem sevenNineExtensionChunks101_flatten :
    sevenNineExtensionChunks101.flatMap id =
      middleFourListPowerset sevenNineExtensionVector101Eligible0 := by
  decide

theorem sevenNineExtensionChunks101_check :
    sevenNineExtensionChunks101.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector101
        sevenNineExtensionVector101Base0
        sevenNineExtensionVector101BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks101
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk101_00_check]
  rw [sevenNineExtensionChunk101_01_check]
  rw [sevenNineExtensionChunk101_02_check]
  rw [sevenNineExtensionChunk101_03_check]
  decide

theorem sevenNineExtensionVector101_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector101Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector101
        sevenNineExtensionVector101Base0
        sevenNineExtensionVector101BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks101_flatten
    sevenNineExtensionChunks101_check

theorem sevenNineExtensionVector101_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector101
      sevenNineExtensionVector101Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector101_base0 (by decide)
    sevenNineExtensionVector101_base_blocker0
    sevenNineExtensionVector101_eligible0
    sevenNineExtensionVector101_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
