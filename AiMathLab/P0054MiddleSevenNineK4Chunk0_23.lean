import AiMathLab.P0054MiddleSevenNineK4Chunk0_22
import AiMathLab.P0054MiddleSevenNineK4Part0_23_0
import AiMathLab.P0054MiddleSevenNineK4Part0_23_1
import AiMathLab.P0054MiddleSevenNineK4Part0_23_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_23_check :
    sevenNineK4ChunkCheck 0 23 = true :=
  sevenNineK4ChunkCheck_of_parts 0 23
    (by decide)
    sevenNineK4_part_0_23_0_check
    sevenNineK4_part_0_23_1_check
    sevenNineK4_part_0_23_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
