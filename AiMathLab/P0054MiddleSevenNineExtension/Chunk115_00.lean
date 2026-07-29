import AiMathLab.P0054MiddleSevenNineExtension.Vector115
import AiMathLab.P0054MiddleSevenNineExtension.Chunk112_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk115_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [3], [3, 6], [3, 5], [3, 5, 6], [2], [2, 6], [2, 5], [2, 5, 6], [2, 3], [2, 3, 6], [2, 3, 5], [2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk115_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector115
        sevenNineExtensionVector115Base0
        sevenNineExtensionVector115BaseBlocker0
        sevenNineExtensionChunk115_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
