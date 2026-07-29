import AiMathLab.P0054MiddleSevenNineK4Chunk0_15
import AiMathLab.P0054MiddleSevenNineK4Part0_16_0
import AiMathLab.P0054MiddleSevenNineK4Part0_16_1
import AiMathLab.P0054MiddleSevenNineK4Part0_16_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_16_check :
    sevenNineK4ChunkCheck 0 16 = true :=
  sevenNineK4ChunkCheck_of_parts 0 16
    (by decide)
    sevenNineK4_part_0_16_0_check
    sevenNineK4_part_0_16_1_check
    sevenNineK4_part_0_16_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
