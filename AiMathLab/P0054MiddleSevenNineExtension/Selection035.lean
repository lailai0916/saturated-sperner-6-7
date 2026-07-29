import AiMathLab.P0054MiddleSevenNineExtension.Chunk035_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk035_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk035_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk035_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection029

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks035 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk035_00, sevenNineExtensionChunk035_01, sevenNineExtensionChunk035_02, sevenNineExtensionChunk035_03]

theorem sevenNineExtensionChunks035_flatten :
    sevenNineExtensionChunks035.flatMap id =
      middleFourListPowerset sevenNineExtensionVector035Eligible0 := by
  decide

theorem sevenNineExtensionChunks035_check :
    sevenNineExtensionChunks035.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector035
        sevenNineExtensionVector035Base0
        sevenNineExtensionVector035BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks035
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk035_00_check]
  rw [sevenNineExtensionChunk035_01_check]
  rw [sevenNineExtensionChunk035_02_check]
  rw [sevenNineExtensionChunk035_03_check]
  decide

theorem sevenNineExtensionVector035_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector035Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector035
        sevenNineExtensionVector035Base0
        sevenNineExtensionVector035BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks035_flatten
    sevenNineExtensionChunks035_check

theorem sevenNineExtensionVector035_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector035
      sevenNineExtensionVector035Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector035_base0 (by decide)
    sevenNineExtensionVector035_base_blocker0
    sevenNineExtensionVector035_eligible0
    sevenNineExtensionVector035_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
