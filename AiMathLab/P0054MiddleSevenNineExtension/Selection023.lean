import AiMathLab.P0054MiddleSevenNineExtension.Chunk023_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk023_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk023_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk023_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection015

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks023 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk023_00, sevenNineExtensionChunk023_01, sevenNineExtensionChunk023_02, sevenNineExtensionChunk023_03]

theorem sevenNineExtensionChunks023_flatten :
    sevenNineExtensionChunks023.flatMap id =
      middleFourListPowerset sevenNineExtensionVector023Eligible0 := by
  decide

theorem sevenNineExtensionChunks023_check :
    sevenNineExtensionChunks023.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector023
        sevenNineExtensionVector023Base0
        sevenNineExtensionVector023BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks023
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk023_00_check]
  rw [sevenNineExtensionChunk023_01_check]
  rw [sevenNineExtensionChunk023_02_check]
  rw [sevenNineExtensionChunk023_03_check]
  decide

theorem sevenNineExtensionVector023_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector023Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector023
        sevenNineExtensionVector023Base0
        sevenNineExtensionVector023BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks023_flatten
    sevenNineExtensionChunks023_check

theorem sevenNineExtensionVector023_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector023
      sevenNineExtensionVector023Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector023_base0 (by decide)
    sevenNineExtensionVector023_base_blocker0
    sevenNineExtensionVector023_eligible0
    sevenNineExtensionVector023_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
