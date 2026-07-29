import AiMathLab.P0054MiddleSevenNineExtension.Vector015
import AiMathLab.P0054MiddleSevenNineExtension.Chunk015_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk015_03 :
    List (List MiddleFourModelPoint) :=
  [[1, 2], [1, 2, 6], [1, 2, 5], [1, 2, 5, 6], [1, 2, 4], [1, 2, 4, 6], [1, 2, 4, 5], [1, 2, 4, 5, 6], [1, 2, 3], [1, 2, 3, 6], [1, 2, 3, 5], [1, 2, 3, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4, 6], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk015_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector015
        sevenNineExtensionVector015Base0
        sevenNineExtensionVector015BaseBlocker0
        sevenNineExtensionChunk015_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
