import AiMathLab.P0054MiddleSevenNineExtension.Vector126
import AiMathLab.P0054MiddleSevenNineExtension.Chunk125_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk126_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [4], [4, 5], [2], [2, 5], [2, 4], [2, 4, 5], [1], [1, 5], [1, 4], [1, 4, 5], [1, 2], [1, 2, 5], [1, 2, 4], [1, 2, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk126_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector126
        sevenNineExtensionVector126Base0
        sevenNineExtensionVector126BaseBlocker0
        sevenNineExtensionChunk126_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
