import AiMathLab.P0054MiddleSevenNineExtension.Vector064
import AiMathLab.P0054MiddleSevenNineExtension.Chunk061_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk064_01 :
    List (List MiddleFourModelPoint) :=
  [[2], [2, 6], [2, 5], [2, 5, 6], [2, 4], [2, 4, 6], [2, 4, 5], [2, 4, 5, 6], [2, 3], [2, 3, 6], [2, 3, 5], [2, 3, 5, 6], [2, 3, 4], [2, 3, 4, 6], [2, 3, 4, 5], [2, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk064_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector064
        sevenNineExtensionVector064Base0
        sevenNineExtensionVector064BaseBlocker0
        sevenNineExtensionChunk064_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
