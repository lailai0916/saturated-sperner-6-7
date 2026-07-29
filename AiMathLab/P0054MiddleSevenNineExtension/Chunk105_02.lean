import AiMathLab.P0054MiddleSevenNineExtension.Vector105
import AiMathLab.P0054MiddleSevenNineExtension.Chunk105_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk105_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 4], [0, 4, 6], [0, 4, 5], [0, 4, 5, 6], [0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 4], [0, 2, 4, 6], [0, 2, 4, 5], [0, 2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk105_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector105
        sevenNineExtensionVector105Base0
        sevenNineExtensionVector105BaseBlocker0
        sevenNineExtensionChunk105_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
