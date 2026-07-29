import AiMathLab.P0054MiddleSevenNineExtension.Vector123
import AiMathLab.P0054MiddleSevenNineExtension.Chunk120_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk123_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [4], [4, 6], [4, 5], [4, 5, 6], [3], [3, 6], [3, 5], [3, 5, 6], [3, 4], [3, 4, 6], [3, 4, 5], [3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk123_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector123
        sevenNineExtensionVector123Base0
        sevenNineExtensionVector123BaseBlocker0
        sevenNineExtensionChunk123_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
