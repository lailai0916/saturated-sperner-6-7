import AiMathLab.P0054MiddleSevenNineExtension.Vector049
import AiMathLab.P0054MiddleSevenNineExtension.Chunk049_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk049_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 4], [0, 4, 6], [0, 4, 5], [0, 4, 5, 6], [0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 3, 4], [0, 3, 4, 6], [0, 3, 4, 5], [0, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk049_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector049
        sevenNineExtensionVector049Base0
        sevenNineExtensionVector049BaseBlocker0
        sevenNineExtensionChunk049_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
