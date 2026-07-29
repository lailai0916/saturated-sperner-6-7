import AiMathLab.P0054MiddleSevenNineExtension.Vector109
import AiMathLab.P0054MiddleSevenNineExtension.Chunk108_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk109_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [3], [3, 5], [2], [2, 5], [2, 3], [2, 3, 5], [1], [1, 5], [1, 3], [1, 3, 5], [1, 2], [1, 2, 5], [1, 2, 3], [1, 2, 3, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk109_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector109
        sevenNineExtensionVector109Base0
        sevenNineExtensionVector109BaseBlocker0
        sevenNineExtensionChunk109_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
