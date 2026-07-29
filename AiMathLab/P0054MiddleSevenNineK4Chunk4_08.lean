import AiMathLab.P0054MiddleSevenNineK4Chunk4_07
import AiMathLab.P0054MiddleSevenNineK4Part4_08_0
import AiMathLab.P0054MiddleSevenNineK4Part4_08_1
import AiMathLab.P0054MiddleSevenNineK4Part4_08_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_4_08_check :
    sevenNineK4ChunkCheck 4 8 = true :=
  sevenNineK4ChunkCheck_of_parts 4 8
    (by decide)
    sevenNineK4_part_4_08_0_check
    sevenNineK4_part_4_08_1_check
    sevenNineK4_part_4_08_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
