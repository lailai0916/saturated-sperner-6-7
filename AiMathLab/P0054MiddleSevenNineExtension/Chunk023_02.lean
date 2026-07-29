import AiMathLab.P0054MiddleSevenNineExtension.Vector023
import AiMathLab.P0054MiddleSevenNineExtension.Chunk023_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk023_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 3], [0, 2, 3, 6], [0, 2, 3, 5], [0, 2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk023_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector023
        sevenNineExtensionVector023Base0
        sevenNineExtensionVector023BaseBlocker0
        sevenNineExtensionChunk023_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
