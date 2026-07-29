import AiMathLab.P0054MiddleSevenNineK4Chunk3_02
import AiMathLab.P0054MiddleSevenNineK4Part3_03_0
import AiMathLab.P0054MiddleSevenNineK4Part3_03_1
import AiMathLab.P0054MiddleSevenNineK4Part3_03_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_3_03_check :
    sevenNineK4ChunkCheck 3 3 = true :=
  sevenNineK4ChunkCheck_of_parts 3 3
    (by decide)
    sevenNineK4_part_3_03_0_check
    sevenNineK4_part_3_03_1_check
    sevenNineK4_part_3_03_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
