import AiMathLab.P0054MiddleSevenNineK4Chunk0_08
import AiMathLab.P0054MiddleSevenNineK4Part0_09_0
import AiMathLab.P0054MiddleSevenNineK4Part0_09_1
import AiMathLab.P0054MiddleSevenNineK4Part0_09_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_09_check :
    sevenNineK4ChunkCheck 0 9 = true :=
  sevenNineK4ChunkCheck_of_parts 0 9
    (by decide)
    sevenNineK4_part_0_09_0_check
    sevenNineK4_part_0_09_1_check
    sevenNineK4_part_0_09_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
