import AiMathLab.P0054MiddleSevenNineExtension.Chunk091_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk091_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk091_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk091_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection088

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks091 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk091_00, sevenNineExtensionChunk091_01, sevenNineExtensionChunk091_02, sevenNineExtensionChunk091_03]

theorem sevenNineExtensionChunks091_flatten :
    sevenNineExtensionChunks091.flatMap id =
      middleFourListPowerset sevenNineExtensionVector091Eligible0 := by
  decide

theorem sevenNineExtensionChunks091_check :
    sevenNineExtensionChunks091.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector091
        sevenNineExtensionVector091Base0
        sevenNineExtensionVector091BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks091
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk091_00_check]
  rw [sevenNineExtensionChunk091_01_check]
  rw [sevenNineExtensionChunk091_02_check]
  rw [sevenNineExtensionChunk091_03_check]
  decide

theorem sevenNineExtensionVector091_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector091Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector091
        sevenNineExtensionVector091Base0
        sevenNineExtensionVector091BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks091_flatten
    sevenNineExtensionChunks091_check

theorem sevenNineExtensionVector091_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector091
      sevenNineExtensionVector091Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector091_base0 (by decide)
    sevenNineExtensionVector091_base_blocker0
    sevenNineExtensionVector091_eligible0
    sevenNineExtensionVector091_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
