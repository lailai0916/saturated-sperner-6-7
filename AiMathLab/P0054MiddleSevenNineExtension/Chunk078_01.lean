import AiMathLab.P0054MiddleSevenNineExtension.Vector078
import AiMathLab.P0054MiddleSevenNineExtension.Chunk073_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk078_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 6], [1, 4], [1, 4, 6], [1, 3], [1, 3, 6], [1, 3, 4], [1, 3, 4, 6], [1, 2], [1, 2, 6], [1, 2, 4], [1, 2, 4, 6], [1, 2, 3], [1, 2, 3, 6], [1, 2, 3, 4], [1, 2, 3, 4, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk078_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector078
        sevenNineExtensionVector078Base0
        sevenNineExtensionVector078BaseBlocker0
        sevenNineExtensionChunk078_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
