import AiMathLab.P0054MiddleSevenNineExtension.Chunk120_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk120_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk120_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk120_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection117

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks120 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk120_00, sevenNineExtensionChunk120_01, sevenNineExtensionChunk120_02, sevenNineExtensionChunk120_03]

theorem sevenNineExtensionChunks120_flatten :
    sevenNineExtensionChunks120.flatMap id =
      middleFourListPowerset sevenNineExtensionVector120Eligible0 := by
  decide

theorem sevenNineExtensionChunks120_check :
    sevenNineExtensionChunks120.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector120
        sevenNineExtensionVector120Base0
        sevenNineExtensionVector120BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks120
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk120_00_check]
  rw [sevenNineExtensionChunk120_01_check]
  rw [sevenNineExtensionChunk120_02_check]
  rw [sevenNineExtensionChunk120_03_check]
  decide

theorem sevenNineExtensionVector120_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector120Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector120
        sevenNineExtensionVector120Base0
        sevenNineExtensionVector120BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks120_flatten
    sevenNineExtensionChunks120_check

theorem sevenNineExtensionVector120_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector120
      sevenNineExtensionVector120Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector120_base0 (by decide)
    sevenNineExtensionVector120_base_blocker0
    sevenNineExtensionVector120_eligible0
    sevenNineExtensionVector120_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
