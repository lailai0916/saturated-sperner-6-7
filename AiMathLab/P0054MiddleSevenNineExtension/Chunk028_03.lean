import AiMathLab.P0054MiddleSevenNineExtension.Vector028
import AiMathLab.P0054MiddleSevenNineExtension.Chunk028_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk028_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 6], [0, 1, 4], [0, 1, 4, 6], [0, 1, 3], [0, 1, 3, 6], [0, 1, 3, 4], [0, 1, 3, 4, 6], [0, 1, 2], [0, 1, 2, 6], [0, 1, 2, 4], [0, 1, 2, 4, 6], [0, 1, 2, 3], [0, 1, 2, 3, 6], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk028_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector028
        sevenNineExtensionVector028Base0
        sevenNineExtensionVector028BaseBlocker0
        sevenNineExtensionChunk028_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
