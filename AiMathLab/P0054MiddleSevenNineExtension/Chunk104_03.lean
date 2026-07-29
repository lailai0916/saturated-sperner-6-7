import AiMathLab.P0054MiddleSevenNineExtension.Vector104
import AiMathLab.P0054MiddleSevenNineExtension.Chunk104_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk104_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 4], [0, 2, 4, 6], [0, 2, 4, 5], [0, 2, 4, 5, 6], [0, 2, 3], [0, 2, 3, 6], [0, 2, 3, 5], [0, 2, 3, 5, 6], [0, 2, 3, 4], [0, 2, 3, 4, 6], [0, 2, 3, 4, 5], [0, 2, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk104_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector104
        sevenNineExtensionVector104Base0
        sevenNineExtensionVector104BaseBlocker0
        sevenNineExtensionChunk104_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
