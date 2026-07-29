import AiMathLab.P0054MiddleSevenNineExtension.Chunk049_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk049_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk049_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk049_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection046

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks049 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk049_00, sevenNineExtensionChunk049_01, sevenNineExtensionChunk049_02, sevenNineExtensionChunk049_03]

theorem sevenNineExtensionChunks049_flatten :
    sevenNineExtensionChunks049.flatMap id =
      middleFourListPowerset sevenNineExtensionVector049Eligible0 := by
  decide

theorem sevenNineExtensionChunks049_check :
    sevenNineExtensionChunks049.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector049
        sevenNineExtensionVector049Base0
        sevenNineExtensionVector049BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks049
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk049_00_check]
  rw [sevenNineExtensionChunk049_01_check]
  rw [sevenNineExtensionChunk049_02_check]
  rw [sevenNineExtensionChunk049_03_check]
  decide

theorem sevenNineExtensionVector049_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector049Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector049
        sevenNineExtensionVector049Base0
        sevenNineExtensionVector049BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks049_flatten
    sevenNineExtensionChunks049_check

theorem sevenNineExtensionVector049_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector049
      sevenNineExtensionVector049Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector049_base0 (by decide)
    sevenNineExtensionVector049_base_blocker0
    sevenNineExtensionVector049_eligible0
    sevenNineExtensionVector049_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
