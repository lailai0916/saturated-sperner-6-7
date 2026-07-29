import AiMathLab.P0054MiddleSevenNineExtension.Chunk092_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk092_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk092_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk092_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection089

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks092 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk092_00, sevenNineExtensionChunk092_01, sevenNineExtensionChunk092_02, sevenNineExtensionChunk092_03]

theorem sevenNineExtensionChunks092_flatten :
    sevenNineExtensionChunks092.flatMap id =
      middleFourListPowerset sevenNineExtensionVector092Eligible0 := by
  decide

theorem sevenNineExtensionChunks092_check :
    sevenNineExtensionChunks092.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector092
        sevenNineExtensionVector092Base0
        sevenNineExtensionVector092BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks092
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk092_00_check]
  rw [sevenNineExtensionChunk092_01_check]
  rw [sevenNineExtensionChunk092_02_check]
  rw [sevenNineExtensionChunk092_03_check]
  decide

theorem sevenNineExtensionVector092_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector092Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector092
        sevenNineExtensionVector092Base0
        sevenNineExtensionVector092BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks092_flatten
    sevenNineExtensionChunks092_check

theorem sevenNineExtensionVector092_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector092
      sevenNineExtensionVector092Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector092_base0 (by decide)
    sevenNineExtensionVector092_base_blocker0
    sevenNineExtensionVector092_eligible0
    sevenNineExtensionVector092_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
