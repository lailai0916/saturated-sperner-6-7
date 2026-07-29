import AiMathLab.P0054MiddleSevenNineExtension.Vector093
import AiMathLab.P0054MiddleSevenNineExtension.Chunk092_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk093_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [4], [4, 5], [3], [3, 5], [3, 4], [3, 4, 5], [0], [0, 5], [0, 4], [0, 4, 5], [0, 3], [0, 3, 5], [0, 3, 4], [0, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk093_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector093
        sevenNineExtensionVector093Base0
        sevenNineExtensionVector093BaseBlocker0
        sevenNineExtensionChunk093_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
