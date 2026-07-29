import AiMathLab.P0054MiddleSevenNineK4Chunk2_02
import AiMathLab.P0054MiddleSevenNineK4Part2_03_0
import AiMathLab.P0054MiddleSevenNineK4Part2_03_1
import AiMathLab.P0054MiddleSevenNineK4Part2_03_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_2_03_check :
    sevenNineK4ChunkCheck 2 3 = true :=
  sevenNineK4ChunkCheck_of_parts 2 3
    (by decide)
    sevenNineK4_part_2_03_0_check
    sevenNineK4_part_2_03_1_check
    sevenNineK4_part_2_03_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
