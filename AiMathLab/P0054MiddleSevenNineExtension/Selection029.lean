import AiMathLab.P0054MiddleSevenNineExtension.Chunk029_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk029_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk029_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk029_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection023

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks029 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk029_00, sevenNineExtensionChunk029_01, sevenNineExtensionChunk029_02, sevenNineExtensionChunk029_03]

theorem sevenNineExtensionChunks029_flatten :
    sevenNineExtensionChunks029.flatMap id =
      middleFourListPowerset sevenNineExtensionVector029Eligible0 := by
  decide

theorem sevenNineExtensionChunks029_check :
    sevenNineExtensionChunks029.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector029
        sevenNineExtensionVector029Base0
        sevenNineExtensionVector029BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks029
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk029_00_check]
  rw [sevenNineExtensionChunk029_01_check]
  rw [sevenNineExtensionChunk029_02_check]
  rw [sevenNineExtensionChunk029_03_check]
  decide

theorem sevenNineExtensionVector029_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector029Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector029
        sevenNineExtensionVector029Base0
        sevenNineExtensionVector029BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks029_flatten
    sevenNineExtensionChunks029_check

theorem sevenNineExtensionVector029_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector029
      sevenNineExtensionVector029Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector029_base0 (by decide)
    sevenNineExtensionVector029_base_blocker0
    sevenNineExtensionVector029_eligible0
    sevenNineExtensionVector029_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
