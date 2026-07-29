import AiMathLab.P0054MiddleSevenNineExtension.Vector101
import AiMathLab.P0054MiddleSevenNineExtension.Chunk098_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk101_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [4], [4, 6], [4, 5], [4, 5, 6], [3], [3, 6], [3, 5], [3, 5, 6], [3, 4], [3, 4, 6], [3, 4, 5], [3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk101_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector101
        sevenNineExtensionVector101Base0
        sevenNineExtensionVector101BaseBlocker0
        sevenNineExtensionChunk101_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
