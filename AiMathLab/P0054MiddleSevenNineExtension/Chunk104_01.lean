import AiMathLab.P0054MiddleSevenNineExtension.Vector104
import AiMathLab.P0054MiddleSevenNineExtension.Chunk101_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk104_01 :
    List (List MiddleFourModelPoint) :=
  [[2], [2, 6], [2, 5], [2, 5, 6], [2, 4], [2, 4, 6], [2, 4, 5], [2, 4, 5, 6], [2, 3], [2, 3, 6], [2, 3, 5], [2, 3, 5, 6], [2, 3, 4], [2, 3, 4, 6], [2, 3, 4, 5], [2, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk104_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector104
        sevenNineExtensionVector104Base0
        sevenNineExtensionVector104BaseBlocker0
        sevenNineExtensionChunk104_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
