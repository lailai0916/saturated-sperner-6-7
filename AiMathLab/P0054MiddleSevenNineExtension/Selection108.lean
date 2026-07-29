import AiMathLab.P0054MiddleSevenNineExtension.Chunk108_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk108_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk108_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk108_03
import AiMathLab.P0054MiddleSevenNineExtension.Selection105

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks108 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk108_00, sevenNineExtensionChunk108_01, sevenNineExtensionChunk108_02, sevenNineExtensionChunk108_03]

theorem sevenNineExtensionChunks108_flatten :
    sevenNineExtensionChunks108.flatMap id =
      middleFourListPowerset sevenNineExtensionVector108Eligible0 := by
  decide

theorem sevenNineExtensionChunks108_check :
    sevenNineExtensionChunks108.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector108
        sevenNineExtensionVector108Base0
        sevenNineExtensionVector108BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks108
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk108_00_check]
  rw [sevenNineExtensionChunk108_01_check]
  rw [sevenNineExtensionChunk108_02_check]
  rw [sevenNineExtensionChunk108_03_check]
  decide

theorem sevenNineExtensionVector108_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector108Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector108
        sevenNineExtensionVector108Base0
        sevenNineExtensionVector108BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks108_flatten
    sevenNineExtensionChunks108_check

theorem sevenNineExtensionVector108_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector108
      sevenNineExtensionVector108Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector108_base0 (by decide)
    sevenNineExtensionVector108_base_blocker0
    sevenNineExtensionVector108_eligible0
    sevenNineExtensionVector108_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
