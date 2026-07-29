import AiMathLab.P0054MiddleSevenNineK4Chunk3_07
import AiMathLab.P0054MiddleSevenNineK4Part3_08_0
import AiMathLab.P0054MiddleSevenNineK4Part3_08_1
import AiMathLab.P0054MiddleSevenNineK4Part3_08_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_3_08_check :
    sevenNineK4ChunkCheck 3 8 = true :=
  sevenNineK4ChunkCheck_of_parts 3 8
    (by decide)
    sevenNineK4_part_3_08_0_check
    sevenNineK4_part_3_08_1_check
    sevenNineK4_part_3_08_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
