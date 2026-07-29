import AiMathLab.P0054MiddleSevenNineK4Chunk0_20
import AiMathLab.P0054MiddleSevenNineK4Part0_21_0
import AiMathLab.P0054MiddleSevenNineK4Part0_21_1
import AiMathLab.P0054MiddleSevenNineK4Part0_21_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_21_check :
    sevenNineK4ChunkCheck 0 21 = true :=
  sevenNineK4ChunkCheck_of_parts 0 21
    (by decide)
    sevenNineK4_part_0_21_0_check
    sevenNineK4_part_0_21_1_check
    sevenNineK4_part_0_21_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
