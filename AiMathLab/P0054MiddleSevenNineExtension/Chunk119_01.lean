import AiMathLab.P0054MiddleSevenNineExtension.Vector119
import AiMathLab.P0054MiddleSevenNineExtension.Chunk117_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk119_01 :
    List (List MiddleFourModelPoint) :=
  [[2], [2, 6], [2, 5], [2, 5, 6], [2, 4], [2, 4, 6], [2, 4, 5], [2, 4, 5, 6], [2, 3], [2, 3, 6], [2, 3, 5], [2, 3, 5, 6], [2, 3, 4], [2, 3, 4, 6], [2, 3, 4, 5], [2, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk119_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector119
        sevenNineExtensionVector119Base0
        sevenNineExtensionVector119BaseBlocker0
        sevenNineExtensionChunk119_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
