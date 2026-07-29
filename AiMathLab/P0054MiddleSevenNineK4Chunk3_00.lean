import AiMathLab.P0054MiddleSevenNineK4Chunk2_08
import AiMathLab.P0054MiddleSevenNineK4Part3_00_0
import AiMathLab.P0054MiddleSevenNineK4Part3_00_1
import AiMathLab.P0054MiddleSevenNineK4Part3_00_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_3_00_check :
    sevenNineK4ChunkCheck 3 0 = true :=
  sevenNineK4ChunkCheck_of_parts 3 0
    (by decide)
    sevenNineK4_part_3_00_0_check
    sevenNineK4_part_3_00_1_check
    sevenNineK4_part_3_00_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
