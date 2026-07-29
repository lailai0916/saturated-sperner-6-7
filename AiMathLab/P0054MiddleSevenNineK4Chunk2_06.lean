import AiMathLab.P0054MiddleSevenNineK4Chunk2_05
import AiMathLab.P0054MiddleSevenNineK4Part2_06_0
import AiMathLab.P0054MiddleSevenNineK4Part2_06_1
import AiMathLab.P0054MiddleSevenNineK4Part2_06_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_2_06_check :
    sevenNineK4ChunkCheck 2 6 = true :=
  sevenNineK4ChunkCheck_of_parts 2 6
    (by decide)
    sevenNineK4_part_2_06_0_check
    sevenNineK4_part_2_06_1_check
    sevenNineK4_part_2_06_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
