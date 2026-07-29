import AiMathLab.P0054MiddleSevenNineK4Chunk3_06
import AiMathLab.P0054MiddleSevenNineK4Part3_07_0
import AiMathLab.P0054MiddleSevenNineK4Part3_07_1
import AiMathLab.P0054MiddleSevenNineK4Part3_07_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_3_07_check :
    sevenNineK4ChunkCheck 3 7 = true :=
  sevenNineK4ChunkCheck_of_parts 3 7
    (by decide)
    sevenNineK4_part_3_07_0_check
    sevenNineK4_part_3_07_1_check
    sevenNineK4_part_3_07_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
