import AiMathLab.P0054MiddleSevenNineK4Chunk0_16
import AiMathLab.P0054MiddleSevenNineK4Part0_17_0
import AiMathLab.P0054MiddleSevenNineK4Part0_17_1
import AiMathLab.P0054MiddleSevenNineK4Part0_17_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_17_check :
    sevenNineK4ChunkCheck 0 17 = true :=
  sevenNineK4ChunkCheck_of_parts 0 17
    (by decide)
    sevenNineK4_part_0_17_0_check
    sevenNineK4_part_0_17_1_check
    sevenNineK4_part_0_17_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
