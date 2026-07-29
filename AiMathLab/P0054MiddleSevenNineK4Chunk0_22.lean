import AiMathLab.P0054MiddleSevenNineK4Chunk0_21
import AiMathLab.P0054MiddleSevenNineK4Part0_22_0
import AiMathLab.P0054MiddleSevenNineK4Part0_22_1
import AiMathLab.P0054MiddleSevenNineK4Part0_22_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_22_check :
    sevenNineK4ChunkCheck 0 22 = true :=
  sevenNineK4ChunkCheck_of_parts 0 22
    (by decide)
    sevenNineK4_part_0_22_0_check
    sevenNineK4_part_0_22_1_check
    sevenNineK4_part_0_22_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
