import AiMathLab.P0054MiddleSevenNineExtension.Vector029
import AiMathLab.P0054MiddleSevenNineExtension.Chunk029_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk029_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 5], [0, 1, 4], [0, 1, 4, 5], [0, 1, 3], [0, 1, 3, 5], [0, 1, 3, 4], [0, 1, 3, 4, 5], [0, 1, 2], [0, 1, 2, 5], [0, 1, 2, 4], [0, 1, 2, 4, 5], [0, 1, 2, 3], [0, 1, 2, 3, 5], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk029_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector029
        sevenNineExtensionVector029Base0
        sevenNineExtensionVector029BaseBlocker0
        sevenNineExtensionChunk029_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
