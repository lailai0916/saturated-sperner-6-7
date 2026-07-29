import AiMathLab.P0054MiddleSevenNineExtension.Vector035
import AiMathLab.P0054MiddleSevenNineExtension.Chunk035_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk035_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 4], [0, 4, 6], [0, 4, 5], [0, 4, 5, 6], [0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 4], [0, 2, 4, 6], [0, 2, 4, 5], [0, 2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk035_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector035
        sevenNineExtensionVector035Base0
        sevenNineExtensionVector035BaseBlocker0
        sevenNineExtensionChunk035_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
