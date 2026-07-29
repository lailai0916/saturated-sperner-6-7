import AiMathLab.P0054MiddleSevenNineExtension.Chunk078_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk078_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk078_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk078_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection067

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks078 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk078_00, sevenNineExtensionChunk078_01, sevenNineExtensionChunk078_02, sevenNineExtensionChunk078_03]

theorem sevenNineExtensionChunks078_flatten :
    sevenNineExtensionChunks078.flatMap id =
      middleFourListPowerset sevenNineExtensionVector078Eligible0 := by
  decide

theorem sevenNineExtensionChunks078_check :
    sevenNineExtensionChunks078.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector078
        sevenNineExtensionVector078Base0
        sevenNineExtensionVector078BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks078
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk078_00_check]
  rw [sevenNineExtensionChunk078_01_check]
  rw [sevenNineExtensionChunk078_02_check]
  rw [sevenNineExtensionChunk078_03_check]
  decide

theorem sevenNineExtensionVector078_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector078Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector078
        sevenNineExtensionVector078Base0
        sevenNineExtensionVector078BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks078_flatten
    sevenNineExtensionChunks078_check

theorem sevenNineExtensionVector078_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector078
      sevenNineExtensionVector078Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector078_base0 (by decide)
    sevenNineExtensionVector078_base_blocker0
    sevenNineExtensionVector078_eligible0
    sevenNineExtensionVector078_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
