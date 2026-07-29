import AiMathLab.P0054MiddleSevenNineK4Chunk0_19
import AiMathLab.P0054MiddleSevenNineK4Part0_20_0
import AiMathLab.P0054MiddleSevenNineK4Part0_20_1
import AiMathLab.P0054MiddleSevenNineK4Part0_20_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_20_check :
    sevenNineK4ChunkCheck 0 20 = true :=
  sevenNineK4ChunkCheck_of_parts 0 20
    (by decide)
    sevenNineK4_part_0_20_0_check
    sevenNineK4_part_0_20_1_check
    sevenNineK4_part_0_20_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
