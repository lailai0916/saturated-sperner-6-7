import AiMathLab.P0054MiddleSevenNineExtension.Chunk060_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk060_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk060_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk060_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection049

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks060 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk060_00, sevenNineExtensionChunk060_01, sevenNineExtensionChunk060_02, sevenNineExtensionChunk060_03]

theorem sevenNineExtensionChunks060_flatten :
    sevenNineExtensionChunks060.flatMap id =
      middleFourListPowerset sevenNineExtensionVector060Eligible0 := by
  decide

theorem sevenNineExtensionChunks060_check :
    sevenNineExtensionChunks060.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector060
        sevenNineExtensionVector060Base0
        sevenNineExtensionVector060BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks060
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk060_00_check]
  rw [sevenNineExtensionChunk060_01_check]
  rw [sevenNineExtensionChunk060_02_check]
  rw [sevenNineExtensionChunk060_03_check]
  decide

theorem sevenNineExtensionVector060_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector060Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector060
        sevenNineExtensionVector060Base0
        sevenNineExtensionVector060BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks060_flatten
    sevenNineExtensionChunks060_check

theorem sevenNineExtensionVector060_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector060
      sevenNineExtensionVector060Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector060_base0 (by decide)
    sevenNineExtensionVector060_base_blocker0
    sevenNineExtensionVector060_eligible0
    sevenNineExtensionVector060_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
