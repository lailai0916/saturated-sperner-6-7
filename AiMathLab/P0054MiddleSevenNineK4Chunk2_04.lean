import AiMathLab.P0054MiddleSevenNineK4Chunk2_03
import AiMathLab.P0054MiddleSevenNineK4Part2_04_0
import AiMathLab.P0054MiddleSevenNineK4Part2_04_1
import AiMathLab.P0054MiddleSevenNineK4Part2_04_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_2_04_check :
    sevenNineK4ChunkCheck 2 4 = true :=
  sevenNineK4ChunkCheck_of_parts 2 4
    (by decide)
    sevenNineK4_part_2_04_0_check
    sevenNineK4_part_2_04_1_check
    sevenNineK4_part_2_04_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
