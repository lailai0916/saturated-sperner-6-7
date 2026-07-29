import AiMathLab.P0054MiddleSevenNineExtension.Vector014
import AiMathLab.P0054MiddleSevenNineExtension.Chunk014_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk014_03 :
    List (List MiddleFourModelPoint) :=
  [[1, 2], [1, 2, 6], [1, 2, 5], [1, 2, 5, 6], [1, 2, 4], [1, 2, 4, 6], [1, 2, 4, 5], [1, 2, 4, 5, 6], [1, 2, 3], [1, 2, 3, 6], [1, 2, 3, 5], [1, 2, 3, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4, 6], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk014_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector014
        sevenNineExtensionVector014Base0
        sevenNineExtensionVector014BaseBlocker0
        sevenNineExtensionChunk014_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
