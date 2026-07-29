import AiMathLab.P0054MiddleSevenNineExtension.Vector014

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionChunk014_00 :
    List (List MiddleFourModelPoint) :=
  [[], [6], [5], [5, 6], [4], [4, 6], [4, 5], [4, 5, 6], [3], [3, 6], [3, 5], [3, 5, 6], [3, 4], [3, 4, 6], [3, 4, 5], [3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionChunk014_00_check :
    sevenNineModelRawChunkCheck sevenNineExtensionVector014
        sevenNineExtensionVector014Base0
        sevenNineExtensionVector014BaseBlocker0
        sevenNineExtensionChunk014_00 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
