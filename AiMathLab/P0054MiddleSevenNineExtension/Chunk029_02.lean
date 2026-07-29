import AiMathLab.P0054MiddleSevenNineExtension.Vector029
import AiMathLab.P0054MiddleSevenNineExtension.Chunk029_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk029_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 5], [0, 4], [0, 4, 5], [0, 3], [0, 3, 5], [0, 3, 4], [0, 3, 4, 5], [0, 2], [0, 2, 5], [0, 2, 4], [0, 2, 4, 5], [0, 2, 3], [0, 2, 3, 5], [0, 2, 3, 4], [0, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk029_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector029
        sevenNineExtensionVector029Base0
        sevenNineExtensionVector029BaseBlocker0
        sevenNineExtensionChunk029_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
