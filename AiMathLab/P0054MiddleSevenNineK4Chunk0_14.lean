import AiMathLab.P0054MiddleSevenNineK4Chunk0_13
import AiMathLab.P0054MiddleSevenNineK4Part0_14_0
import AiMathLab.P0054MiddleSevenNineK4Part0_14_1
import AiMathLab.P0054MiddleSevenNineK4Part0_14_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_14_check :
    sevenNineK4ChunkCheck 0 14 = true :=
  sevenNineK4ChunkCheck_of_parts 0 14
    (by decide)
    sevenNineK4_part_0_14_0_check
    sevenNineK4_part_0_14_1_check
    sevenNineK4_part_0_14_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
