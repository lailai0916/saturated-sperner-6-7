import AiMathLab.P0054MiddleSevenNineK4Chunk1_02
import AiMathLab.P0054MiddleSevenNineK4Part1_03_0
import AiMathLab.P0054MiddleSevenNineK4Part1_03_1
import AiMathLab.P0054MiddleSevenNineK4Part1_03_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_1_03_check :
    sevenNineK4ChunkCheck 1 3 = true :=
  sevenNineK4ChunkCheck_of_parts 1 3
    (by decide)
    sevenNineK4_part_1_03_0_check
    sevenNineK4_part_1_03_1_check
    sevenNineK4_part_1_03_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
