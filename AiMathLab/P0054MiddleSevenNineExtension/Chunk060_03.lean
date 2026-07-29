import AiMathLab.P0054MiddleSevenNineExtension.Vector060
import AiMathLab.P0054MiddleSevenNineExtension.Chunk060_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk060_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 6], [0, 1, 4], [0, 1, 4, 6], [0, 1, 3], [0, 1, 3, 6], [0, 1, 3, 4], [0, 1, 3, 4, 6], [0, 1, 2], [0, 1, 2, 6], [0, 1, 2, 4], [0, 1, 2, 4, 6], [0, 1, 2, 3], [0, 1, 2, 3, 6], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk060_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector060
        sevenNineExtensionVector060Base0
        sevenNineExtensionVector060BaseBlocker0
        sevenNineExtensionChunk060_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
