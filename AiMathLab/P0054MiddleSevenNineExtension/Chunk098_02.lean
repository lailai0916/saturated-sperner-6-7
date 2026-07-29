import AiMathLab.P0054MiddleSevenNineExtension.Vector098
import AiMathLab.P0054MiddleSevenNineExtension.Chunk098_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk098_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 5], [0, 4], [0, 4, 5], [0, 3], [0, 3, 5], [0, 3, 4], [0, 3, 4, 5], [0, 2], [0, 2, 5], [0, 2, 4], [0, 2, 4, 5], [0, 2, 3], [0, 2, 3, 5], [0, 2, 3, 4], [0, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk098_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector098
        sevenNineExtensionVector098Base0
        sevenNineExtensionVector098BaseBlocker0
        sevenNineExtensionChunk098_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
