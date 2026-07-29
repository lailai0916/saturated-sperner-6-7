import AiMathLab.P0054MiddleSevenNineExtension.Vector089
import AiMathLab.P0054MiddleSevenNineExtension.Chunk087_00

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk089_00 :
    List (List MiddleFourModelPoint) :=
  [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3], [0], [0, 3], [0, 2], [0, 2, 3], [0, 1], [0, 1, 3], [0, 1, 2], [0, 1, 2, 3]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk089_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector089
        sevenNineExtensionVector089Base0
        sevenNineExtensionVector089BaseBlocker0
        sevenNineExtensionChunk089_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
