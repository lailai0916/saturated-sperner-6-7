import AiMathLab.P0054MiddleSevenNineK4Part3_02_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks 27 old-row pairs from one K4 certificate chunk.
theorem sevenNineK4_part_3_03_1_check :
    sevenNineK4ChunkPartCheck 3 3 1 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineK4Finite
