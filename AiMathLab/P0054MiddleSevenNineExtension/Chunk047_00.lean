import AiMathLab.P0054MiddleSevenNineExtension.Vector047
import AiMathLab.P0054MiddleSevenNineExtension.Chunk046_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk047_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [4], [4, 6], [4, 5], [4, 5, 6], [3], [3, 6], [3, 5], [3, 5, 6], [3, 4], [3, 4, 6], [3, 4, 5], [3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk047_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector047
        sevenNineExtensionVector047Base0
        sevenNineExtensionVector047BaseBlocker0
        sevenNineExtensionChunk047_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
