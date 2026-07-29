import AiMathLab.P0054MiddleSevenNineExtension.Chunk067_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk067_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk067_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk067_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection064

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks067 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk067_00, sevenNineExtensionChunk067_01, sevenNineExtensionChunk067_02, sevenNineExtensionChunk067_03]

theorem sevenNineExtensionChunks067_flatten :
    sevenNineExtensionChunks067.flatMap id =
      middleFourListPowerset sevenNineExtensionVector067Eligible0 := by
  decide

theorem sevenNineExtensionChunks067_check :
    sevenNineExtensionChunks067.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector067
        sevenNineExtensionVector067Base0
        sevenNineExtensionVector067BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks067
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk067_00_check]
  rw [sevenNineExtensionChunk067_01_check]
  rw [sevenNineExtensionChunk067_02_check]
  rw [sevenNineExtensionChunk067_03_check]
  decide

theorem sevenNineExtensionVector067_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector067Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector067
        sevenNineExtensionVector067Base0
        sevenNineExtensionVector067BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks067_flatten
    sevenNineExtensionChunks067_check

theorem sevenNineExtensionVector067_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector067
      sevenNineExtensionVector067Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector067_base0 (by decide)
    sevenNineExtensionVector067_base_blocker0
    sevenNineExtensionVector067_eligible0
    sevenNineExtensionVector067_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
