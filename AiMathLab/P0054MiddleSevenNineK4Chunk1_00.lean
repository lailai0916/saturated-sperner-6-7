import AiMathLab.P0054MiddleSevenNineK4Chunk0_26
import AiMathLab.P0054MiddleSevenNineK4Part1_00_0
import AiMathLab.P0054MiddleSevenNineK4Part1_00_1
import AiMathLab.P0054MiddleSevenNineK4Part1_00_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_1_00_check :
    sevenNineK4ChunkCheck 1 0 = true :=
  sevenNineK4ChunkCheck_of_parts 1 0
    (by decide)
    sevenNineK4_part_1_00_0_check
    sevenNineK4_part_1_00_1_check
    sevenNineK4_part_1_00_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
