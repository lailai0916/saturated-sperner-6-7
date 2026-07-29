import AiMathLab.P0054MiddleSevenNineExtension.Vector095
import AiMathLab.P0054MiddleSevenNineExtension.Chunk095_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk095_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 5], [0, 4], [0, 4, 5], [0, 3], [0, 3, 5], [0, 3, 4], [0, 3, 4, 5], [0, 2], [0, 2, 5], [0, 2, 4], [0, 2, 4, 5], [0, 2, 3], [0, 2, 3, 5], [0, 2, 3, 4], [0, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk095_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector095
        sevenNineExtensionVector095Base0
        sevenNineExtensionVector095BaseBlocker0
        sevenNineExtensionChunk095_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
