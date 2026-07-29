import AiMathLab.P0054MiddleSevenNineExtension.Chunk132_00
import AiMathLab.P0054MiddleSevenNineExtension.Selection129

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks132 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk132_00]

theorem sevenNineExtensionChunks132_flatten :
    sevenNineExtensionChunks132.flatMap id =
      middleFourListPowerset sevenNineExtensionVector132Eligible0 := by
  decide

theorem sevenNineExtensionChunks132_check :
    sevenNineExtensionChunks132.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector132
        sevenNineExtensionVector132Base0
        sevenNineExtensionVector132BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks132
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk132_00_check]


theorem sevenNineExtensionVector132_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector132Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector132
        sevenNineExtensionVector132Base0
        sevenNineExtensionVector132BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks132_flatten
    sevenNineExtensionChunks132_check

theorem sevenNineExtensionVector132_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector132
      sevenNineExtensionVector132Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector132_base0 (by decide)
    sevenNineExtensionVector132_base_blocker0
    sevenNineExtensionVector132_eligible0
    sevenNineExtensionVector132_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
