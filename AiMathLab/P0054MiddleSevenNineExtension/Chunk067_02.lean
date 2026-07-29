import AiMathLab.P0054MiddleSevenNineExtension.Vector067
import AiMathLab.P0054MiddleSevenNineExtension.Chunk067_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk067_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 4], [0, 4, 6], [0, 4, 5], [0, 4, 5, 6], [0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 3, 4], [0, 3, 4, 6], [0, 3, 4, 5], [0, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk067_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector067
        sevenNineExtensionVector067Base0
        sevenNineExtensionVector067BaseBlocker0
        sevenNineExtensionChunk067_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
