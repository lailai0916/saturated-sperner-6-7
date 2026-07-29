import AiMathLab.P0054MiddleSevenNineExtension.Chunk089_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection087

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks089 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk089_00]

theorem sevenNineExtensionChunks089_flatten :
    sevenNineExtensionChunks089.flatMap id =
      middleFourListPowerset sevenNineExtensionVector089Eligible0 := by
  decide

theorem sevenNineExtensionChunks089_check :
    sevenNineExtensionChunks089.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector089
        sevenNineExtensionVector089Base0
        sevenNineExtensionVector089BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks089
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk089_00_check]


theorem sevenNineExtensionVector089_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector089Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector089
        sevenNineExtensionVector089Base0
        sevenNineExtensionVector089BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks089_flatten
    sevenNineExtensionChunks089_check

theorem sevenNineExtensionVector089_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector089
      sevenNineExtensionVector089Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector089_base0 (by decide)
    sevenNineExtensionVector089_base_blocker0
    sevenNineExtensionVector089_eligible0
    sevenNineExtensionVector089_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
