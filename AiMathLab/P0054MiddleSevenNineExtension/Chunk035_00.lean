import AiMathLab.P0054MiddleSevenNineExtension.Vector035
import AiMathLab.P0054MiddleSevenNineExtension.Chunk032_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk035_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [4], [4, 6], [4, 5], [4, 5, 6], [2], [2, 6], [2, 5], [2, 5, 6], [2, 4], [2, 4, 6], [2, 4, 5], [2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk035_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector035
        sevenNineExtensionVector035Base0
        sevenNineExtensionVector035BaseBlocker0
        sevenNineExtensionChunk035_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
