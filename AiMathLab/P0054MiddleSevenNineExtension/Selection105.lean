import AiMathLab.P0054MiddleSevenNineExtension.Chunk105_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk105_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk105_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk105_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection101

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks105 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk105_00, sevenNineExtensionChunk105_01, sevenNineExtensionChunk105_02, sevenNineExtensionChunk105_03]

theorem sevenNineExtensionChunks105_flatten :
    sevenNineExtensionChunks105.flatMap id =
      middleFourListPowerset sevenNineExtensionVector105Eligible0 := by
  decide

theorem sevenNineExtensionChunks105_check :
    sevenNineExtensionChunks105.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector105
        sevenNineExtensionVector105Base0
        sevenNineExtensionVector105BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks105
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk105_00_check]
  rw [sevenNineExtensionChunk105_01_check]
  rw [sevenNineExtensionChunk105_02_check]
  rw [sevenNineExtensionChunk105_03_check]
  decide

theorem sevenNineExtensionVector105_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector105Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector105
        sevenNineExtensionVector105Base0
        sevenNineExtensionVector105BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks105_flatten
    sevenNineExtensionChunks105_check

theorem sevenNineExtensionVector105_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector105
      sevenNineExtensionVector105Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector105_base0 (by decide)
    sevenNineExtensionVector105_base_blocker0
    sevenNineExtensionVector105_eligible0
    sevenNineExtensionVector105_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
