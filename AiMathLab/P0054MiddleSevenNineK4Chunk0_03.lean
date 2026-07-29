import AiMathLab.P0054MiddleSevenNineK4Chunk0_02
import AiMathLab.P0054MiddleSevenNineK4Part0_03_0
import AiMathLab.P0054MiddleSevenNineK4Part0_03_1
import AiMathLab.P0054MiddleSevenNineK4Part0_03_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_03_check :
    sevenNineK4ChunkCheck 0 3 = true :=
  sevenNineK4ChunkCheck_of_parts 0 3
    (by decide)
    sevenNineK4_part_0_03_0_check
    sevenNineK4_part_0_03_1_check
    sevenNineK4_part_0_03_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
