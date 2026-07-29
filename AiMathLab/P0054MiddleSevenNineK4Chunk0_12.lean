import AiMathLab.P0054MiddleSevenNineK4Chunk0_11
import AiMathLab.P0054MiddleSevenNineK4Part0_12_0
import AiMathLab.P0054MiddleSevenNineK4Part0_12_1
import AiMathLab.P0054MiddleSevenNineK4Part0_12_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_12_check :
    sevenNineK4ChunkCheck 0 12 = true :=
  sevenNineK4ChunkCheck_of_parts 0 12
    (by decide)
    sevenNineK4_part_0_12_0_check
    sevenNineK4_part_0_12_1_check
    sevenNineK4_part_0_12_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
