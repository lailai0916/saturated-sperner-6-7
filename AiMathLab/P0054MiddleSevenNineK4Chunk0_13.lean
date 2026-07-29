import AiMathLab.P0054MiddleSevenNineK4Chunk0_12
import AiMathLab.P0054MiddleSevenNineK4Part0_13_0
import AiMathLab.P0054MiddleSevenNineK4Part0_13_1
import AiMathLab.P0054MiddleSevenNineK4Part0_13_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_13_check :
    sevenNineK4ChunkCheck 0 13 = true :=
  sevenNineK4ChunkCheck_of_parts 0 13
    (by decide)
    sevenNineK4_part_0_13_0_check
    sevenNineK4_part_0_13_1_check
    sevenNineK4_part_0_13_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
