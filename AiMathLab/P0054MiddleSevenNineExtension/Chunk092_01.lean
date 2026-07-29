import AiMathLab.P0054MiddleSevenNineExtension.Vector092
import AiMathLab.P0054MiddleSevenNineExtension.Chunk091_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk092_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 6], [1, 5], [1, 5, 6], [1, 4], [1, 4, 6], [1, 4, 5], [1, 4, 5, 6], [1, 2], [1, 2, 6], [1, 2, 5], [1, 2, 5, 6], [1, 2, 4], [1, 2, 4, 6], [1, 2, 4, 5], [1, 2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk092_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector092
        sevenNineExtensionVector092Base0
        sevenNineExtensionVector092BaseBlocker0
        sevenNineExtensionChunk092_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
