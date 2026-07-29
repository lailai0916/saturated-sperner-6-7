import AiMathLab.P0054MiddleSevenNineExtension.Vector099
import AiMathLab.P0054MiddleSevenNineExtension.Chunk098_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk099_00 :
    List (List MiddleFourModelPoint) :=
  [[], [4], [3], [3, 4], [1], [1, 4], [1, 3], [1, 3, 4], [0], [0, 4], [0, 3], [0, 3, 4], [0, 1], [0, 1, 4], [0, 1, 3], [0, 1, 3, 4]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk099_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector099
        sevenNineExtensionVector099Base0
        sevenNineExtensionVector099BaseBlocker0
        sevenNineExtensionChunk099_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
