import AiMathLab.P0054MiddleSevenNineExtension.Vector092
import AiMathLab.P0054MiddleSevenNineExtension.Chunk092_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk092_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 4], [0, 4, 6], [0, 4, 5], [0, 4, 5, 6], [0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 4], [0, 2, 4, 6], [0, 2, 4, 5], [0, 2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk092_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector092
        sevenNineExtensionVector092Base0
        sevenNineExtensionVector092BaseBlocker0
        sevenNineExtensionChunk092_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
