import AiMathLab.P0054MiddleSevenNineExtension.Vector096
import AiMathLab.P0054MiddleSevenNineExtension.Chunk095_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk096_00 :
    List (List MiddleFourModelPoint) :=
  [[], [4], [3], [3, 4], [2], [2, 4], [2, 3], [2, 3, 4], [0], [0, 4], [0, 3], [0, 3, 4], [0, 2], [0, 2, 4], [0, 2, 3], [0, 2, 3, 4]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk096_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector096
        sevenNineExtensionVector096Base0
        sevenNineExtensionVector096BaseBlocker0
        sevenNineExtensionChunk096_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
