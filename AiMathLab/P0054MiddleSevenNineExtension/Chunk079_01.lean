import AiMathLab.P0054MiddleSevenNineExtension.Vector079
import AiMathLab.P0054MiddleSevenNineExtension.Chunk078_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk079_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 5], [1, 4], [1, 4, 5], [1, 3], [1, 3, 5], [1, 3, 4], [1, 3, 4, 5], [1, 2], [1, 2, 5], [1, 2, 4], [1, 2, 4, 5], [1, 2, 3], [1, 2, 3, 5], [1, 2, 3, 4], [1, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk079_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector079
        sevenNineExtensionVector079Base0
        sevenNineExtensionVector079BaseBlocker0
        sevenNineExtensionChunk079_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
