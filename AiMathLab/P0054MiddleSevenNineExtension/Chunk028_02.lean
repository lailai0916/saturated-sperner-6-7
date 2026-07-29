import AiMathLab.P0054MiddleSevenNineExtension.Vector028
import AiMathLab.P0054MiddleSevenNineExtension.Chunk028_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk028_02 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 4], [0, 4, 6], [0, 3], [0, 3, 6], [0, 3, 4], [0, 3, 4, 6], [0, 2], [0, 2, 6], [0, 2, 4], [0, 2, 4, 6], [0, 2, 3], [0, 2, 3, 6], [0, 2, 3, 4], [0, 2, 3, 4, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk028_02_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector028
        sevenNineExtensionVector028Base0
        sevenNineExtensionVector028BaseBlocker0
        sevenNineExtensionChunk028_02 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
