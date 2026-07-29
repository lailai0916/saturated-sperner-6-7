import AiMathLab.P0054MiddleSevenNineExtension.Vector115
import AiMathLab.P0054MiddleSevenNineExtension.Chunk115_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk115_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 3], [0, 2, 3, 6], [0, 2, 3, 5], [0, 2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk115_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector115
        sevenNineExtensionVector115Base0
        sevenNineExtensionVector115BaseBlocker0
        sevenNineExtensionChunk115_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
