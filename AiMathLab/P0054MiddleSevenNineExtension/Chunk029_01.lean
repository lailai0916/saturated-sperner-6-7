import AiMathLab.P0054MiddleSevenNineExtension.Vector029
import AiMathLab.P0054MiddleSevenNineExtension.Chunk028_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk029_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 5], [1, 4], [1, 4, 5], [1, 3], [1, 3, 5], [1, 3, 4], [1, 3, 4, 5], [1, 2], [1, 2, 5], [1, 2, 4], [1, 2, 4, 5], [1, 2, 3], [1, 2, 3, 5], [1, 2, 3, 4], [1, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk029_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector029
        sevenNineExtensionVector029Base0
        sevenNineExtensionVector029BaseBlocker0
        sevenNineExtensionChunk029_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
