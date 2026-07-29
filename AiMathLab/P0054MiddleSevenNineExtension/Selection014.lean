import AiMathLab.P0054MiddleSevenNineExtension.Chunk014_00
import AiMathLab.P0054MiddleSevenNineExtension.Chunk014_01
import AiMathLab.P0054MiddleSevenNineExtension.Chunk014_02
import AiMathLab.P0054MiddleSevenNineExtension.Chunk014_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunks014 :
    List (List (List MiddleFourModelPoint)) :=
  [sevenNineExtensionChunk014_00, sevenNineExtensionChunk014_01, sevenNineExtensionChunk014_02, sevenNineExtensionChunk014_03]

theorem sevenNineExtensionChunks014_flatten :
    sevenNineExtensionChunks014.flatMap id =
      middleFourListPowerset sevenNineExtensionVector014Eligible0 := by
  decide

theorem sevenNineExtensionChunks014_check :
    sevenNineExtensionChunks014.all
      (sevenNineModelRawChunkCheck sevenNineExtensionVector014
        sevenNineExtensionVector014Base0
        sevenNineExtensionVector014BaseBlocker0) = true := by
  unfold sevenNineExtensionChunks014
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionChunk014_00_check]
  rw [sevenNineExtensionChunk014_01_check]
  rw [sevenNineExtensionChunk014_02_check]
  rw [sevenNineExtensionChunk014_03_check]
  decide

theorem sevenNineExtensionVector014_raw0_check :
    (middleFourListPowerset
      sevenNineExtensionVector014Eligible0).all
      (sevenNineModelRawOldCheck sevenNineExtensionVector014
        sevenNineExtensionVector014Base0
        sevenNineExtensionVector014BaseBlocker0) = true :=
  sevenNineModelRawSelectionCheck_of_chunks _ _ _ _ _
    sevenNineExtensionChunks014_flatten
    sevenNineExtensionChunks014_check

theorem sevenNineExtensionVector014_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector014
      sevenNineExtensionVector014Selected0 = true :=
  sevenNineModelSelectionCheck_of_raw _ _ _ _ _
    sevenNineExtensionVector014_base0 (by decide)
    sevenNineExtensionVector014_base_blocker0
    sevenNineExtensionVector014_eligible0
    sevenNineExtensionVector014_raw0_check

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
