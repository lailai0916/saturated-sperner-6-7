import AiMathLab.P0054MiddleSevenNineK4Chunk4_04
import AiMathLab.P0054MiddleSevenNineK4Part4_05_0
import AiMathLab.P0054MiddleSevenNineK4Part4_05_1
import AiMathLab.P0054MiddleSevenNineK4Part4_05_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_4_05_check :
    sevenNineK4ChunkCheck 4 5 = true :=
  sevenNineK4ChunkCheck_of_parts 4 5
    (by decide)
    sevenNineK4_part_4_05_0_check
    sevenNineK4_part_4_05_1_check
    sevenNineK4_part_4_05_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
