import AiMathLab.P0054FanoAdjacentSevenSixChunk09

namespace AiMathLab.P0054.FanoAdjacentSevenSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks one block of 81 labelled Fano selections.
theorem fanoSevenSix_chunk_10_check :
    fanoSevenSixChunkCheck 10 = true := by
  decide

end AiMathLab.P0054.FanoAdjacentSevenSixFinite
