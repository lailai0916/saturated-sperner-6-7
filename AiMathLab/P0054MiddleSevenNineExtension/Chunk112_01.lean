import AiMathLab.P0054MiddleSevenNineExtension.Vector112
import AiMathLab.P0054MiddleSevenNineExtension.Chunk109_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk112_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 6], [1, 5], [1, 5, 6], [1, 4], [1, 4, 6], [1, 4, 5], [1, 4, 5, 6], [1, 2], [1, 2, 6], [1, 2, 5], [1, 2, 5, 6], [1, 2, 4], [1, 2, 4, 6], [1, 2, 4, 5], [1, 2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk112_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector112
        sevenNineExtensionVector112Base0
        sevenNineExtensionVector112BaseBlocker0
        sevenNineExtensionChunk112_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
