import AiMathLab.P0054MiddleSevenNineExtension.Vector073
import AiMathLab.P0054MiddleSevenNineExtension.Chunk073_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk073_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 3], [0, 2, 3, 6], [0, 2, 3, 5], [0, 2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk073_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector073
        sevenNineExtensionVector073Base0
        sevenNineExtensionVector073BaseBlocker0
        sevenNineExtensionChunk073_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
