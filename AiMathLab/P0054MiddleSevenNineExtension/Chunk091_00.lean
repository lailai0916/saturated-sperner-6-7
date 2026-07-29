import AiMathLab.P0054MiddleSevenNineExtension.Vector091
import AiMathLab.P0054MiddleSevenNineExtension.Chunk088_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk091_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [4], [4, 6], [4, 5], [4, 5, 6], [2], [2, 6], [2, 5], [2, 5, 6], [2, 4], [2, 4, 6], [2, 4, 5], [2, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk091_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector091
        sevenNineExtensionVector091Base0
        sevenNineExtensionVector091BaseBlocker0
        sevenNineExtensionChunk091_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
