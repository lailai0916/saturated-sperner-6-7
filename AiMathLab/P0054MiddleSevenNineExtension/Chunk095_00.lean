import AiMathLab.P0054MiddleSevenNineExtension.Vector095
import AiMathLab.P0054MiddleSevenNineExtension.Chunk092_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk095_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [4], [4, 5], [3], [3, 5], [3, 4], [3, 4, 5], [2], [2, 5], [2, 4], [2, 4, 5], [2, 3], [2, 3, 5], [2, 3, 4], [2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk095_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector095
        sevenNineExtensionVector095Base0
        sevenNineExtensionVector095BaseBlocker0
        sevenNineExtensionChunk095_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
