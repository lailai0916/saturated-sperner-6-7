import AiMathLab.P0054MiddleSevenNineExtension.Vector049
import AiMathLab.P0054MiddleSevenNineExtension.Chunk049_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk049_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 6], [0, 1, 5], [0, 1, 5, 6], [0, 1, 4], [0, 1, 4, 6], [0, 1, 4, 5], [0, 1, 4, 5, 6], [0, 1, 3], [0, 1, 3, 6], [0, 1, 3, 5], [0, 1, 3, 5, 6], [0, 1, 3, 4], [0, 1, 3, 4, 6], [0, 1, 3, 4, 5], [0, 1, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk049_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector049
        sevenNineExtensionVector049Base0
        sevenNineExtensionVector049BaseBlocker0
        sevenNineExtensionChunk049_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
