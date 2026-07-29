import AiMathLab.P0054MiddleSevenNineK4Chunk0_17
import AiMathLab.P0054MiddleSevenNineK4Part0_18_0
import AiMathLab.P0054MiddleSevenNineK4Part0_18_1
import AiMathLab.P0054MiddleSevenNineK4Part0_18_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_18_check :
    sevenNineK4ChunkCheck 0 18 = true :=
  sevenNineK4ChunkCheck_of_parts 0 18
    (by decide)
    sevenNineK4_part_0_18_0_check
    sevenNineK4_part_0_18_1_check
    sevenNineK4_part_0_18_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
