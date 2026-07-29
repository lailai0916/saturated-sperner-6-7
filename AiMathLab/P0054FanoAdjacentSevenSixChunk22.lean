import AiMathLab.P0054FanoAdjacentSevenSixChunk21

namespace AiMathLab.P0054.FanoAdjacentSevenSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks one block of 81 labelled Fano selections.
theorem fanoSevenSix_chunk_22_check :
    fanoSevenSixChunkCheck 22 = true := by
  decide

end AiMathLab.P0054.FanoAdjacentSevenSixFinite
