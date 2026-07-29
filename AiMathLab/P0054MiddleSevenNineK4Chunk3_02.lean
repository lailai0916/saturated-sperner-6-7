import AiMathLab.P0054MiddleSevenNineK4Chunk3_01
import AiMathLab.P0054MiddleSevenNineK4Part3_02_0
import AiMathLab.P0054MiddleSevenNineK4Part3_02_1
import AiMathLab.P0054MiddleSevenNineK4Part3_02_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_3_02_check :
    sevenNineK4ChunkCheck 3 2 = true :=
  sevenNineK4ChunkCheck_of_parts 3 2
    (by decide)
    sevenNineK4_part_3_02_0_check
    sevenNineK4_part_3_02_1_check
    sevenNineK4_part_3_02_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
