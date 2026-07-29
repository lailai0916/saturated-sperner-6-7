import AiMathLab.P0054MiddleSevenNineK4Chunk0_10
import AiMathLab.P0054MiddleSevenNineK4Part0_11_0
import AiMathLab.P0054MiddleSevenNineK4Part0_11_1
import AiMathLab.P0054MiddleSevenNineK4Part0_11_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_11_check :
    sevenNineK4ChunkCheck 0 11 = true :=
  sevenNineK4ChunkCheck_of_parts 0 11
    (by decide)
    sevenNineK4_part_0_11_0_check
    sevenNineK4_part_0_11_1_check
    sevenNineK4_part_0_11_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
