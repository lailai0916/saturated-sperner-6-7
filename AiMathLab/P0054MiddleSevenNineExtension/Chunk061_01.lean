import AiMathLab.P0054MiddleSevenNineExtension.Vector061
import AiMathLab.P0054MiddleSevenNineExtension.Chunk060_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk061_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 5], [1, 4], [1, 4, 5], [1, 3], [1, 3, 5], [1, 3, 4], [1, 3, 4, 5], [1, 2], [1, 2, 5], [1, 2, 4], [1, 2, 4, 5], [1, 2, 3], [1, 2, 3, 5], [1, 2, 3, 4], [1, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk061_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector061
        sevenNineExtensionVector061Base0
        sevenNineExtensionVector061BaseBlocker0
        sevenNineExtensionChunk061_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
