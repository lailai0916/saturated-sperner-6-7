import AiMathLab.P0054MiddleSevenNineK4Chunk0_18
import AiMathLab.P0054MiddleSevenNineK4Part0_19_0
import AiMathLab.P0054MiddleSevenNineK4Part0_19_1
import AiMathLab.P0054MiddleSevenNineK4Part0_19_2

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_chunk_0_19_check :
    sevenNineK4ChunkCheck 0 19 = true :=
  sevenNineK4ChunkCheck_of_parts 0 19
    (by decide)
    sevenNineK4_part_0_19_0_check
    sevenNineK4_part_0_19_1_check
    sevenNineK4_part_0_19_2_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
