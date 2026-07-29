import AiMathLab.P0054MiddleSevenNineExtension.Vector125
import AiMathLab.P0054MiddleSevenNineExtension.Chunk125_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk125_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 3], [0, 2, 3, 6], [0, 2, 3, 5], [0, 2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk125_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector125
        sevenNineExtensionVector125Base0
        sevenNineExtensionVector125BaseBlocker0
        sevenNineExtensionChunk125_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
