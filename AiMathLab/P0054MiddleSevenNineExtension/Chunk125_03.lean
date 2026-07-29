import AiMathLab.P0054MiddleSevenNineExtension.Vector125
import AiMathLab.P0054MiddleSevenNineExtension.Chunk125_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk125_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 6], [0, 1, 5], [0, 1, 5, 6], [0, 1, 3], [0, 1, 3, 6], [0, 1, 3, 5], [0, 1, 3, 5, 6], [0, 1, 2], [0, 1, 2, 6], [0, 1, 2, 5], [0, 1, 2, 5, 6], [0, 1, 2, 3], [0, 1, 2, 3, 6], [0, 1, 2, 3, 5], [0, 1, 2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk125_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector125
        sevenNineExtensionVector125Base0
        sevenNineExtensionVector125BaseBlocker0
        sevenNineExtensionChunk125_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
