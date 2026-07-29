import AiMathLab.P0054MiddleSevenNineK4Chunk0_00
import AiMathLab.P0054MiddleSevenNineK4Part0_01_0
import AiMathLab.P0054MiddleSevenNineK4Part0_01_1
import AiMathLab.P0054MiddleSevenNineK4Part0_01_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_01_check :
    sevenNineK4ChunkCheck 0 1 = true :=
  sevenNineK4ChunkCheck_of_parts 0 1
    (by decide)
    sevenNineK4_part_0_01_0_check
    sevenNineK4_part_0_01_1_check
    sevenNineK4_part_0_01_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
