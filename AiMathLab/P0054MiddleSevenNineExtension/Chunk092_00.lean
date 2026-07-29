import AiMathLab.P0054MiddleSevenNineExtension.Vector092
import AiMathLab.P0054MiddleSevenNineExtension.Chunk091_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk092_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [4], [4, 6], [4, 5], [4, 5, 6], [2], [2, 6], [2, 5], [2, 5, 6], [2, 4], [2, 4, 6], [2, 4, 5], [2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk092_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector092
        sevenNineExtensionVector092Base0
        sevenNineExtensionVector092BaseBlocker0
        sevenNineExtensionChunk092_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
