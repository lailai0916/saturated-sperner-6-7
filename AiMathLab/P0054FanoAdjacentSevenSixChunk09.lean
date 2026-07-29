import AiMathLab.P0054FanoAdjacentSevenSixChunk08

namespace AiMathLab.P0054.FanoAdjacentSevenSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks one block of 81 labelled Fano selections.
theorem fanoSevenSix_chunk_09_check :
    fanoSevenSixChunkCheck 9 = true := by
  decide

end AiMathLab.P0054.FanoAdjacentSevenSixFinite
