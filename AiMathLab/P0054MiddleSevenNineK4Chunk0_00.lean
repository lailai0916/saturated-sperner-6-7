import AiMathLab.P0054MiddleSevenNineK4FiniteCore
import AiMathLab.P0054MiddleSevenNineK4Part0_00_0
import AiMathLab.P0054MiddleSevenNineK4Part0_00_1
import AiMathLab.P0054MiddleSevenNineK4Part0_00_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_00_check :
    sevenNineK4ChunkCheck 0 0 = true :=
  sevenNineK4ChunkCheck_of_parts 0 0
    (by decide)
    sevenNineK4_part_0_00_0_check
    sevenNineK4_part_0_00_1_check
    sevenNineK4_part_0_00_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
