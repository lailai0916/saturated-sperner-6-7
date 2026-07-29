import AiMathLab.P0054MiddleSevenNineExtension.Vector132
import AiMathLab.P0054MiddleSevenNineExtension.Chunk131_02

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk132_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [4], [4, 5], [1], [1, 5], [1, 4], [1, 4, 5], [0], [0, 5], [0, 4], [0, 4, 5], [0, 1], [0, 1, 5], [0, 1, 4], [0, 1, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk132_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector132
        sevenNineExtensionVector132Base0
        sevenNineExtensionVector132BaseBlocker0
        sevenNineExtensionChunk132_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
