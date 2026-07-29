import AiMathLab.P0054MiddleSevenNineExtension.Vector055
import AiMathLab.P0054MiddleSevenNineExtension.Chunk055_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk055_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 2], [0, 2, 6], [0, 2, 5], [0, 2, 5, 6], [0, 2, 3], [0, 2, 3, 6], [0, 2, 3, 5], [0, 2, 3, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk055_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector055
        sevenNineExtensionVector055Base0
        sevenNineExtensionVector055BaseBlocker0
        sevenNineExtensionChunk055_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
