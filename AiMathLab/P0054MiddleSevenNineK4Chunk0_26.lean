import AiMathLab.P0054MiddleSevenNineK4Chunk0_25
import AiMathLab.P0054MiddleSevenNineK4Part0_26_0
import AiMathLab.P0054MiddleSevenNineK4Part0_26_1
import AiMathLab.P0054MiddleSevenNineK4Part0_26_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_26_check :
    sevenNineK4ChunkCheck 0 26 = true :=
  sevenNineK4ChunkCheck_of_parts 0 26
    (by decide)
    sevenNineK4_part_0_26_0_check
    sevenNineK4_part_0_26_1_check
    sevenNineK4_part_0_26_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
