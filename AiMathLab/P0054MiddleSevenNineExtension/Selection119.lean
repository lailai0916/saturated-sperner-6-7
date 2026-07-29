import AiMathLab.P0054MiddleSevenNineExtension.Chunk119_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk119_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk119_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk119_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection115

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks119 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk119_00, sevenNineExtensionChunk119_01, sevenNineExtensionChunk119_02, sevenNineExtensionChunk119_03]

theorem sevenNineExtensionChunks119_flatten :
    sevenNineExtensionChunks119.flatMap id =
      middleFourListPowerset sevenNineExtensionVector119Eligible0 := by
  decide

theorem sevenNineExtensionChunks119_check :
    sevenNineExtensionChunks119.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector119
        sevenNineExtensionVector119Base0
        sevenNineExtensionVector119BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks119
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk119_00_check]
  rw [sevenNineExtensionChunk119_01_check]
  rw [sevenNineExtensionChunk119_02_check]
  rw [sevenNineExtensionChunk119_03_check]
  decide

theorem sevenNineExtensionVector119_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector119Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector119
        sevenNineExtensionVector119Base0
        sevenNineExtensionVector119BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks119_flatten
    sevenNineExtensionChunks119_check

theorem sevenNineExtensionVector119_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector119
      sevenNineExtensionVector119Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector119_base0 (by decide)
    sevenNineExtensionVector119_base_blocker0
    sevenNineExtensionVector119_eligible0
    sevenNineExtensionVector119_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
