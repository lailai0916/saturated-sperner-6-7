import AiMathLab.P0054MiddleSevenNineExtension.Vector020
import AiMathLab.P0054MiddleSevenNineExtension.Chunk020_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk020_02 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 6], [1, 5], [1, 5, 6], [1, 4], [1, 4, 6], [1, 4, 5], [1, 4, 5, 6], [1, 3], [1, 3, 6], [1, 3, 5], [1, 3, 5, 6], [1, 3, 4], [1, 3, 4, 6], [1, 3, 4, 5], [1, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk020_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector020
        sevenNineExtensionVector020Base0
        sevenNineExtensionVector020BaseBlocker0
        sevenNineExtensionChunk020_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
