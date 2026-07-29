import AiMathLab.P0054MiddleSevenNineExtension.Vector088
import AiMathLab.P0054MiddleSevenNineExtension.Chunk079_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk088_00 :
    List (List MiddleFourModelPoint) :=
  [[], [4], [2], [2, 4], [1], [1, 4], [1, 2], [1, 2, 4], [0], [0, 4], [0, 2], [0, 2, 4], [0, 1], [0, 1, 4], [0, 1, 2], [0, 1, 2, 4]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk088_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector088
        sevenNineExtensionVector088Base0
        sevenNineExtensionVector088BaseBlocker0
        sevenNineExtensionChunk088_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
