import AiMathLab.P0054MiddleSevenNineK4Chunk0_05
import AiMathLab.P0054MiddleSevenNineK4Part0_06_0
import AiMathLab.P0054MiddleSevenNineK4Part0_06_1
import AiMathLab.P0054MiddleSevenNineK4Part0_06_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_06_check :
    sevenNineK4ChunkCheck 0 6 = true :=
  sevenNineK4ChunkCheck_of_parts 0 6
    (by decide)
    sevenNineK4_part_0_06_0_check
    sevenNineK4_part_0_06_1_check
    sevenNineK4_part_0_06_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
