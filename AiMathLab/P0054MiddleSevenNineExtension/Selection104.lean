import AiMathLab.P0054MiddleSevenNineExtension.Chunk104_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk104_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk104_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk104_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection099

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks104 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk104_00, sevenNineExtensionChunk104_01, sevenNineExtensionChunk104_02, sevenNineExtensionChunk104_03]

theorem sevenNineExtensionChunks104_flatten :
    sevenNineExtensionChunks104.flatMap id =
      middleFourListPowerset sevenNineExtensionVector104Eligible0 := by
  decide

theorem sevenNineExtensionChunks104_check :
    sevenNineExtensionChunks104.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector104
        sevenNineExtensionVector104Base0
        sevenNineExtensionVector104BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks104
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk104_00_check]
  rw [sevenNineExtensionChunk104_01_check]
  rw [sevenNineExtensionChunk104_02_check]
  rw [sevenNineExtensionChunk104_03_check]
  decide

theorem sevenNineExtensionVector104_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector104Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector104
        sevenNineExtensionVector104Base0
        sevenNineExtensionVector104BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks104_flatten
    sevenNineExtensionChunks104_check

theorem sevenNineExtensionVector104_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector104
      sevenNineExtensionVector104Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector104_base0 (by decide)
    sevenNineExtensionVector104_base_blocker0
    sevenNineExtensionVector104_eligible0
    sevenNineExtensionVector104_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
