import AiMathLab.P0054MiddleSevenNineExtension.Chunk015_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk015_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk015_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk015_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks015 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk015_00, sevenNineExtensionChunk015_01, sevenNineExtensionChunk015_02, sevenNineExtensionChunk015_03]

theorem sevenNineExtensionChunks015_flatten :
    sevenNineExtensionChunks015.flatMap id =
      middleFourListPowerset sevenNineExtensionVector015Eligible0 := by
  decide

theorem sevenNineExtensionChunks015_check :
    sevenNineExtensionChunks015.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector015
        sevenNineExtensionVector015Base0
        sevenNineExtensionVector015BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks015
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk015_00_check]
  rw [sevenNineExtensionChunk015_01_check]
  rw [sevenNineExtensionChunk015_02_check]
  rw [sevenNineExtensionChunk015_03_check]
  decide

theorem sevenNineExtensionVector015_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector015Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector015
        sevenNineExtensionVector015Base0
        sevenNineExtensionVector015BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks015_flatten
    sevenNineExtensionChunks015_check

theorem sevenNineExtensionVector015_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector015
      sevenNineExtensionVector015Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector015_base0 (by decide)
    sevenNineExtensionVector015_base_blocker0
    sevenNineExtensionVector015_eligible0
    sevenNineExtensionVector015_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
