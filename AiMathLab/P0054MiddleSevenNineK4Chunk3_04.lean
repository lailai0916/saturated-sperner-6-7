import AiMathLab.P0054MiddleSevenNineK4Chunk3_03
import AiMathLab.P0054MiddleSevenNineK4Part3_04_0
import AiMathLab.P0054MiddleSevenNineK4Part3_04_1
import AiMathLab.P0054MiddleSevenNineK4Part3_04_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_3_04_check :
    sevenNineK4ChunkCheck 3 4 = true :=
  sevenNineK4ChunkCheck_of_parts 3 4
    (by decide)
    sevenNineK4_part_3_04_0_check
    sevenNineK4_part_3_04_1_check
    sevenNineK4_part_3_04_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
