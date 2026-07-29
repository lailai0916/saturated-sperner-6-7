import AiMathLab.P0054MiddleSevenNineExtension.Vector106
import AiMathLab.P0054MiddleSevenNineExtension.Chunk105_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk106_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [4], [4, 5], [3], [3, 5], [3, 4], [3, 4, 5], [1], [1, 5], [1, 4], [1, 4, 5], [1, 3], [1, 3, 5], [1, 3, 4], [1, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk106_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector106
        sevenNineExtensionVector106Base0
        sevenNineExtensionVector106BaseBlocker0
        sevenNineExtensionChunk106_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
