import AiMathLab.P0054MiddleSevenNineExtension.Vector121
import AiMathLab.P0054MiddleSevenNineExtension.Chunk120_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk121_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [4], [4, 5], [3], [3, 5], [3, 4], [3, 4, 5], [2], [2, 5], [2, 4], [2, 4, 5], [2, 3], [2, 3, 5], [2, 3, 4], [2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk121_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector121
        sevenNineExtensionVector121Base0
        sevenNineExtensionVector121BaseBlocker0
        sevenNineExtensionChunk121_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
