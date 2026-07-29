import AiMathLab.P0054MiddleSevenNineK4Chunk1_06
import AiMathLab.P0054MiddleSevenNineK4Part1_07_0
import AiMathLab.P0054MiddleSevenNineK4Part1_07_1
import AiMathLab.P0054MiddleSevenNineK4Part1_07_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_1_07_check :
    sevenNineK4ChunkCheck 1 7 = true :=
  sevenNineK4ChunkCheck_of_parts 1 7
    (by decide)
    sevenNineK4_part_1_07_0_check
    sevenNineK4_part_1_07_1_check
    sevenNineK4_part_1_07_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
