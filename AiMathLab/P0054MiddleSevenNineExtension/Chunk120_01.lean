import AiMathLab.P0054MiddleSevenNineExtension.Vector120
import AiMathLab.P0054MiddleSevenNineExtension.Chunk119_03

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk120_01 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 6], [1, 5], [1, 5, 6], [1, 4], [1, 4, 6], [1, 4, 5], [1, 4, 5, 6], [1, 3], [1, 3, 6], [1, 3, 5], [1, 3, 5, 6], [1, 3, 4], [1, 3, 4, 6], [1, 3, 4, 5], [1, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk120_01_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector120
        sevenNineExtensionVector120Base0
        sevenNineExtensionVector120BaseBlocker0
        sevenNineExtensionChunk120_01 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
