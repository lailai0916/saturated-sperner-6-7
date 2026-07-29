import AiMathLab.P0054MiddleSevenNineExtension.Vector073
import AiMathLab.P0054MiddleSevenNineExtension.Chunk067_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk073_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [3], [3, 6], [3, 5], [3, 5, 6], [2], [2, 6], [2, 5], [2, 5, 6], [2, 3], [2, 3, 6], [2, 3, 5], [2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk073_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector073
        sevenNineExtensionVector073Base0
        sevenNineExtensionVector073BaseBlocker0
        sevenNineExtensionChunk073_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
