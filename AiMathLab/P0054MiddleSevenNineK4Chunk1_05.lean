import AiMathLab.P0054MiddleSevenNineK4Chunk1_04
import AiMathLab.P0054MiddleSevenNineK4Part1_05_0
import AiMathLab.P0054MiddleSevenNineK4Part1_05_1
import AiMathLab.P0054MiddleSevenNineK4Part1_05_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_1_05_check :
    sevenNineK4ChunkCheck 1 5 = true :=
  sevenNineK4ChunkCheck_of_parts 1 5
    (by decide)
    sevenNineK4_part_1_05_0_check
    sevenNineK4_part_1_05_1_check
    sevenNineK4_part_1_05_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
