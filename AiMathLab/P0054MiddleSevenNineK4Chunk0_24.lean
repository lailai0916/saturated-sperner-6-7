import AiMathLab.P0054MiddleSevenNineK4Chunk0_23
import AiMathLab.P0054MiddleSevenNineK4Part0_24_0
import AiMathLab.P0054MiddleSevenNineK4Part0_24_1
import AiMathLab.P0054MiddleSevenNineK4Part0_24_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_24_check :
    sevenNineK4ChunkCheck 0 24 = true :=
  sevenNineK4ChunkCheck_of_parts 0 24
    (by decide)
    sevenNineK4_part_0_24_0_check
    sevenNineK4_part_0_24_1_check
    sevenNineK4_part_0_24_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
