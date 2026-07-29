import AiMathLab.P0054MiddleSevenNineExtension.Chunk065_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk065_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk065_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk065_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection061

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks065 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk065_00, sevenNineExtensionChunk065_01, sevenNineExtensionChunk065_02, sevenNineExtensionChunk065_03]

theorem sevenNineExtensionChunks065_flatten :
    sevenNineExtensionChunks065.flatMap id =
      middleFourListPowerset sevenNineExtensionVector065Eligible0 := by
  decide

theorem sevenNineExtensionChunks065_check :
    sevenNineExtensionChunks065.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector065
        sevenNineExtensionVector065Base0
        sevenNineExtensionVector065BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks065
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk065_00_check]
  rw [sevenNineExtensionChunk065_01_check]
  rw [sevenNineExtensionChunk065_02_check]
  rw [sevenNineExtensionChunk065_03_check]
  decide

theorem sevenNineExtensionVector065_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector065Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector065
        sevenNineExtensionVector065Base0
        sevenNineExtensionVector065BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks065_flatten
    sevenNineExtensionChunks065_check

theorem sevenNineExtensionVector065_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector065
      sevenNineExtensionVector065Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector065_base0 (by decide)
    sevenNineExtensionVector065_base_blocker0
    sevenNineExtensionVector065_eligible0
    sevenNineExtensionVector065_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
