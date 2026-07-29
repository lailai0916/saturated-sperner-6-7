import AiMathLab.P0054MiddleSevenNineExtension.Chunk112_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk112_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk112_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk112_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection108

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks112 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk112_00, sevenNineExtensionChunk112_01, sevenNineExtensionChunk112_02, sevenNineExtensionChunk112_03]

theorem sevenNineExtensionChunks112_flatten :
    sevenNineExtensionChunks112.flatMap id =
      middleFourListPowerset sevenNineExtensionVector112Eligible0 := by
  decide

theorem sevenNineExtensionChunks112_check :
    sevenNineExtensionChunks112.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector112
        sevenNineExtensionVector112Base0
        sevenNineExtensionVector112BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks112
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk112_00_check]
  rw [sevenNineExtensionChunk112_01_check]
  rw [sevenNineExtensionChunk112_02_check]
  rw [sevenNineExtensionChunk112_03_check]
  decide

theorem sevenNineExtensionVector112_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector112Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector112
        sevenNineExtensionVector112Base0
        sevenNineExtensionVector112BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks112_flatten
    sevenNineExtensionChunks112_check

theorem sevenNineExtensionVector112_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector112
      sevenNineExtensionVector112Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector112_base0 (by decide)
    sevenNineExtensionVector112_base_blocker0
    sevenNineExtensionVector112_eligible0
    sevenNineExtensionVector112_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
