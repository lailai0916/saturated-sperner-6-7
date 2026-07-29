import AiMathLab.P0054MiddleSevenNineExtension.Vector119
import AiMathLab.P0054MiddleSevenNineExtension.Chunk115_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk119_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [4], [4, 6], [4, 5], [4, 5, 6], [3], [3, 6], [3, 5], [3, 5, 6], [3, 4], [3, 4, 6], [3, 4, 5], [3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk119_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector119
        sevenNineExtensionVector119Base0
        sevenNineExtensionVector119BaseBlocker0
        sevenNineExtensionChunk119_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
