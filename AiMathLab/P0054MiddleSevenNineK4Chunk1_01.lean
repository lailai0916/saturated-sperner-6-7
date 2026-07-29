import AiMathLab.P0054MiddleSevenNineK4Chunk1_00
import AiMathLab.P0054MiddleSevenNineK4Part1_01_0
import AiMathLab.P0054MiddleSevenNineK4Part1_01_1
import AiMathLab.P0054MiddleSevenNineK4Part1_01_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_1_01_check :
    sevenNineK4ChunkCheck 1 1 = true :=
  sevenNineK4ChunkCheck_of_parts 1 1
    (by decide)
    sevenNineK4_part_1_01_0_check
    sevenNineK4_part_1_01_1_check
    sevenNineK4_part_1_01_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
