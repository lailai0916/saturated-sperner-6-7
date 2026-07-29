import AiMathLab.P0054MiddleSevenNineExtension.Vector028
import AiMathLab.P0054MiddleSevenNineExtension.Chunk023_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk028_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [4], [4, 6], [3], [3, 6], [3, 4], [3, 4, 6], [2], [2, 6], [2, 4], [2, 4, 6], [2, 3], [2, 3, 6], [2, 3, 4], [2, 3, 4, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk028_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector028
        sevenNineExtensionVector028Base0
        sevenNineExtensionVector028BaseBlocker0
        sevenNineExtensionChunk028_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
