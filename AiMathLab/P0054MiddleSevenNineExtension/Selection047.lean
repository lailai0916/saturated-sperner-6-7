import AiMathLab.P0054MiddleSevenNineExtension.Chunk047_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk047_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk047_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk047_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection035

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks047 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk047_00, sevenNineExtensionChunk047_01, sevenNineExtensionChunk047_02, sevenNineExtensionChunk047_03]

theorem sevenNineExtensionChunks047_flatten :
    sevenNineExtensionChunks047.flatMap id =
      middleFourListPowerset sevenNineExtensionVector047Eligible0 := by
  decide

theorem sevenNineExtensionChunks047_check :
    sevenNineExtensionChunks047.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector047
        sevenNineExtensionVector047Base0
        sevenNineExtensionVector047BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks047
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk047_00_check]
  rw [sevenNineExtensionChunk047_01_check]
  rw [sevenNineExtensionChunk047_02_check]
  rw [sevenNineExtensionChunk047_03_check]
  decide

theorem sevenNineExtensionVector047_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector047Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector047
        sevenNineExtensionVector047Base0
        sevenNineExtensionVector047BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks047_flatten
    sevenNineExtensionChunks047_check

theorem sevenNineExtensionVector047_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector047
      sevenNineExtensionVector047Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector047_base0 (by decide)
    sevenNineExtensionVector047_base_blocker0
    sevenNineExtensionVector047_eligible0
    sevenNineExtensionVector047_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
