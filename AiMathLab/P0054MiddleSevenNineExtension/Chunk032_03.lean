import AiMathLab.P0054MiddleSevenNineExtension.Vector032
import AiMathLab.P0054MiddleSevenNineExtension.Chunk032_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk032_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 6], [0, 1, 5], [0, 1, 5, 6], [0, 1, 4], [0, 1, 4, 6], [0, 1, 4, 5], [0, 1, 4, 5, 6], [0, 1, 3], [0, 1, 3, 6], [0, 1, 3, 5], [0, 1, 3, 5, 6], [0, 1, 3, 4], [0, 1, 3, 4, 6], [0, 1, 3, 4, 5], [0, 1, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk032_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector032
        sevenNineExtensionVector032Base0
        sevenNineExtensionVector032BaseBlocker0
        sevenNineExtensionChunk032_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
