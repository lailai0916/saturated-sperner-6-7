import AiMathLab.P0054MiddleSevenNineK4Chunk0_14
import AiMathLab.P0054MiddleSevenNineK4Part0_15_0
import AiMathLab.P0054MiddleSevenNineK4Part0_15_1
import AiMathLab.P0054MiddleSevenNineK4Part0_15_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_15_check :
    sevenNineK4ChunkCheck 0 15 = true :=
  sevenNineK4ChunkCheck_of_parts 0 15
    (by decide)
    sevenNineK4_part_0_15_0_check
    sevenNineK4_part_0_15_1_check
    sevenNineK4_part_0_15_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
