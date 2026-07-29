import AiMathLab.P0054MiddleSevenNineK4Chunk1_01
import AiMathLab.P0054MiddleSevenNineK4Part1_02_0
import AiMathLab.P0054MiddleSevenNineK4Part1_02_1
import AiMathLab.P0054MiddleSevenNineK4Part1_02_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_1_02_check :
    sevenNineK4ChunkCheck 1 2 = true :=
  sevenNineK4ChunkCheck_of_parts 1 2
    (by decide)
    sevenNineK4_part_1_02_0_check
    sevenNineK4_part_1_02_1_check
    sevenNineK4_part_1_02_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
