import AiMathLab.P0054MiddleSevenNineExtension.Chunk020_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk020_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk020_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk020_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection014

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks020 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk020_00, sevenNineExtensionChunk020_01, sevenNineExtensionChunk020_02, sevenNineExtensionChunk020_03]

theorem sevenNineExtensionChunks020_flatten :
    sevenNineExtensionChunks020.flatMap id =
      middleFourListPowerset sevenNineExtensionVector020Eligible0 := by
  decide

theorem sevenNineExtensionChunks020_check :
    sevenNineExtensionChunks020.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector020
        sevenNineExtensionVector020Base0
        sevenNineExtensionVector020BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks020
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk020_00_check]
  rw [sevenNineExtensionChunk020_01_check]
  rw [sevenNineExtensionChunk020_02_check]
  rw [sevenNineExtensionChunk020_03_check]
  decide

theorem sevenNineExtensionVector020_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector020Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector020
        sevenNineExtensionVector020Base0
        sevenNineExtensionVector020BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks020_flatten
    sevenNineExtensionChunks020_check

theorem sevenNineExtensionVector020_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector020
      sevenNineExtensionVector020Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector020_base0 (by decide)
    sevenNineExtensionVector020_base_blocker0
    sevenNineExtensionVector020_eligible0
    sevenNineExtensionVector020_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
