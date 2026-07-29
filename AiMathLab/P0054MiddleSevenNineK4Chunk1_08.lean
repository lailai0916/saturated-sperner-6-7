import AiMathLab.P0054MiddleSevenNineK4Chunk1_07
import AiMathLab.P0054MiddleSevenNineK4Part1_08_0
import AiMathLab.P0054MiddleSevenNineK4Part1_08_1
import AiMathLab.P0054MiddleSevenNineK4Part1_08_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_1_08_check :
    sevenNineK4ChunkCheck 1 8 = true :=
  sevenNineK4ChunkCheck_of_parts 1 8
    (by decide)
    sevenNineK4_part_1_08_0_check
    sevenNineK4_part_1_08_1_check
    sevenNineK4_part_1_08_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
