import AiMathLab.P0054MiddleSevenNineExtension.Vector101
import AiMathLab.P0054MiddleSevenNineExtension.Chunk101_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk101_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 4], [0, 4, 6], [0, 4, 5], [0, 4, 5, 6], [0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 3, 4], [0, 3, 4, 6], [0, 3, 4, 5], [0, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk101_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector101
        sevenNineExtensionVector101Base0
        sevenNineExtensionVector101BaseBlocker0
        sevenNineExtensionChunk101_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
