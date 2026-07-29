import AiMathLab.P0054MiddleSevenNineExtension.Vector131
import AiMathLab.P0054MiddleSevenNineExtension.Chunk131_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk131_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 6], [0, 1, 5], [0, 1, 5, 6], [0, 1, 3], [0, 1, 3, 6], [0, 1, 3, 5], [0, 1, 3, 5, 6], [0, 1, 2], [0, 1, 2, 6], [0, 1, 2, 5], [0, 1, 2, 5, 6], [0, 1, 2, 3], [0, 1, 2, 3, 6], [0, 1, 2, 3, 5], [0, 1, 2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk131_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector131
        sevenNineExtensionVector131Base0
        sevenNineExtensionVector131BaseBlocker0
        sevenNineExtensionChunk131_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
