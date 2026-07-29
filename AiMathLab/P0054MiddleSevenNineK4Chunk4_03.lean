import AiMathLab.P0054MiddleSevenNineK4Chunk4_02
import AiMathLab.P0054MiddleSevenNineK4Part4_03_0
import AiMathLab.P0054MiddleSevenNineK4Part4_03_1
import AiMathLab.P0054MiddleSevenNineK4Part4_03_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_4_03_check :
    sevenNineK4ChunkCheck 4 3 = true :=
  sevenNineK4ChunkCheck_of_parts 4 3
    (by decide)
    sevenNineK4_part_4_03_0_check
    sevenNineK4_part_4_03_1_check
    sevenNineK4_part_4_03_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
