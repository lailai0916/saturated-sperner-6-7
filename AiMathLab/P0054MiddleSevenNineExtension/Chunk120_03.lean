import AiMathLab.P0054MiddleSevenNineExtension.Vector120
import AiMathLab.P0054MiddleSevenNineExtension.Chunk120_01

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk120_03 :
    List (List MiddleFourModelPoint) :=
  [[0, 1], [0, 1, 6], [0, 1, 5], [0, 1, 5, 6], [0, 1, 4], [0, 1, 4, 6], [0, 1, 4, 5], [0, 1, 4, 5, 6], [0, 1, 3], [0, 1, 3, 6], [0, 1, 3, 5], [0, 1, 3, 5, 6], [0, 1, 3, 4], [0, 1, 3, 4, 6], [0, 1, 3, 4, 5], [0, 1, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk120_03_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector120
        sevenNineExtensionVector120Base0
        sevenNineExtensionVector120BaseBlocker0
        sevenNineExtensionChunk120_03 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
