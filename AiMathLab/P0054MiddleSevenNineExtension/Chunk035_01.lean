import AiMathLab.P0054MiddleSevenNineExtension.Vector035
import AiMathLab.P0054MiddleSevenNineExtension.Chunk032_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk035_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 6], [1, 5], [1, 5, 6], [1, 4], [1, 4, 6], [1, 4, 5], [1, 4, 5, 6], [1, 2], [1, 2, 6], [1, 2, 5], [1, 2, 5, 6], [1, 2, 4], [1, 2, 4, 6], [1, 2, 4, 5], [1, 2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk035_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector035
        sevenNineExtensionVector035Base0
        sevenNineExtensionVector035BaseBlocker0
        sevenNineExtensionChunk035_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
