import AiMathLab.P0054MiddleSevenNineK4Chunk0_06
import AiMathLab.P0054MiddleSevenNineK4Part0_07_0
import AiMathLab.P0054MiddleSevenNineK4Part0_07_1
import AiMathLab.P0054MiddleSevenNineK4Part0_07_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_07_check :
    sevenNineK4ChunkCheck 0 7 = true :=
  sevenNineK4ChunkCheck_of_parts 0 7
    (by decide)
    sevenNineK4_part_0_07_0_check
    sevenNineK4_part_0_07_1_check
    sevenNineK4_part_0_07_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
