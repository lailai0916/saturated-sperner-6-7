import AiMathLab.P0054MiddleSevenNineExtension.Vector098
import AiMathLab.P0054MiddleSevenNineExtension.Chunk098_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk098_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 5], [0, 1, 4], [0, 1, 4, 5], [0, 1, 3], [0, 1, 3, 5], [0, 1, 3, 4], [0, 1, 3, 4, 5], [0, 1, 2], [0, 1, 2, 5], [0, 1, 2, 4], [0, 1, 2, 4, 5], [0, 1, 2, 3], [0, 1, 2, 3, 5], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk098_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector098
        sevenNineExtensionVector098Base0
        sevenNineExtensionVector098BaseBlocker0
        sevenNineExtensionChunk098_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
