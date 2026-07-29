import AiMathLab.P0054MiddleSevenNineExtension.Chunk055_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk055_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk055_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk055_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection047

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks055 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk055_00, sevenNineExtensionChunk055_01, sevenNineExtensionChunk055_02, sevenNineExtensionChunk055_03]

theorem sevenNineExtensionChunks055_flatten :
    sevenNineExtensionChunks055.flatMap id =
      middleFourListPowerset sevenNineExtensionVector055Eligible0 := by
  decide

theorem sevenNineExtensionChunks055_check :
    sevenNineExtensionChunks055.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector055
        sevenNineExtensionVector055Base0
        sevenNineExtensionVector055BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks055
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk055_00_check]
  rw [sevenNineExtensionChunk055_01_check]
  rw [sevenNineExtensionChunk055_02_check]
  rw [sevenNineExtensionChunk055_03_check]
  decide

theorem sevenNineExtensionVector055_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector055Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector055
        sevenNineExtensionVector055Base0
        sevenNineExtensionVector055BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks055_flatten
    sevenNineExtensionChunks055_check

theorem sevenNineExtensionVector055_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector055
      sevenNineExtensionVector055Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector055_base0 (by decide)
    sevenNineExtensionVector055_base_blocker0
    sevenNineExtensionVector055_eligible0
    sevenNineExtensionVector055_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
