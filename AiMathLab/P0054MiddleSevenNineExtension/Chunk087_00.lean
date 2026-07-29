import AiMathLab.P0054MiddleSevenNineExtension.Vector087
import AiMathLab.P0054MiddleSevenNineExtension.Chunk079_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk087_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [2], [2, 5], [1], [1, 5], [1, 2], [1, 2, 5], [0], [0, 5], [0, 2], [0, 2, 5], [0, 1], [0, 1, 5], [0, 1, 2], [0, 1, 2, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk087_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector087
        sevenNineExtensionVector087Base0
        sevenNineExtensionVector087BaseBlocker0
        sevenNineExtensionChunk087_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
