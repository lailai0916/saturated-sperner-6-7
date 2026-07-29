import AiMathLab.P0054MiddleSevenNineExtension.Vector119
import AiMathLab.P0054MiddleSevenNineExtension.Chunk119_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk119_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 4], [0, 2, 4, 6], [0, 2, 4, 5], [0, 2, 4, 5, 6], [0, 2, 3], [0, 2, 3, 6], [0, 2, 3, 5], [0, 2, 3, 5, 6], [0, 2, 3, 4], [0, 2, 3, 4, 6], [0, 2, 3, 4, 5], [0, 2, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk119_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector119
        sevenNineExtensionVector119Base0
        sevenNineExtensionVector119BaseBlocker0
        sevenNineExtensionChunk119_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
