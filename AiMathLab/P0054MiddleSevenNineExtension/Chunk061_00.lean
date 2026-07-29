import AiMathLab.P0054MiddleSevenNineExtension.Vector061
import AiMathLab.P0054MiddleSevenNineExtension.Chunk060_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk061_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [4], [4, 5], [3], [3, 5], [3, 4], [3, 4, 5], [2], [2, 5], [2, 4], [2, 4, 5], [2, 3], [2, 3, 5], [2, 3, 4], [2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk061_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector061
        sevenNineExtensionVector061Base0
        sevenNineExtensionVector061BaseBlocker0
        sevenNineExtensionChunk061_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
