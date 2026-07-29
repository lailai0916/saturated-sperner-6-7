import AiMathLab.P0054MiddleSevenNineK4Part1_01_0

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks 27 old-row pairs from one K4 certificate chunk.
theorem sevenNineK4_part_1_01_2_check :
    sevenNineK4ChunkPartCheck 1 1 2 = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineK4Finite
