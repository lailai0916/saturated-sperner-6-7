import AiMathLab.P0054MiddleSevenNineExtension.Vector073
import AiMathLab.P0054MiddleSevenNineExtension.Chunk067_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk073_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 6], [1, 5], [1, 5, 6], [1, 3], [1, 3, 6], [1, 3, 5], [1, 3, 5, 6], [1, 2], [1, 2, 6], [1, 2, 5], [1, 2, 5, 6], [1, 2, 3], [1, 2, 3, 6], [1, 2, 3, 5], [1, 2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk073_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector073
        sevenNineExtensionVector073Base0
        sevenNineExtensionVector073BaseBlocker0
        sevenNineExtensionChunk073_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
