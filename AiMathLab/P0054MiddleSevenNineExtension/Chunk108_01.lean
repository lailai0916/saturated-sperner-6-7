import AiMathLab.P0054MiddleSevenNineExtension.Vector108
import AiMathLab.P0054MiddleSevenNineExtension.Chunk106_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk108_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 6], [1, 4], [1, 4, 6], [1, 3], [1, 3, 6], [1, 3, 4], [1, 3, 4, 6], [1, 2], [1, 2, 6], [1, 2, 4], [1, 2, 4, 6], [1, 2, 3], [1, 2, 3, 6], [1, 2, 3, 4], [1, 2, 3, 4, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk108_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector108
        sevenNineExtensionVector108Base0
        sevenNineExtensionVector108BaseBlocker0
        sevenNineExtensionChunk108_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
